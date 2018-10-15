From iris.algebra Require Export ofe monoid.
From stdpp Require Import finite.
Set Default Proof Using "Type".

Class PCore (A : Type) := pcore : A → option A.
Hint Mode PCore ! : typeclass_instances.
Instance: Params (@pcore) 2.

Class Op (A : Type) := op : A → A → A.
Hint Mode Op ! : typeclass_instances.
Instance: Params (@op) 2.
Infix "⋅" := op (at level 50, left associativity) : stdpp_scope.
Notation "(⋅)" := op (only parsing) : stdpp_scope.

(* The inclusion quantifies over [A], not [option A].  This means we do not get
   reflexivity.  However, if we used [option A], the following would no longer
   hold:
     x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2
*)
Definition included `{Equiv A, Op A} (x y : A) := ∃ z, y ≡ x ⋅ z.
Infix "≼" := included (at level 70) : stdpp_scope.
Notation "(≼)" := included (only parsing) : stdpp_scope.
Hint Extern 0 (_ ≼ _) => reflexivity.
Instance: Params (@included) 3.

Class ValidN (A : Type) := validN : nat → A → Prop.
Hint Mode ValidN ! : typeclass_instances.
Instance: Params (@validN) 3.
Notation "✓{ n } x" := (validN n x)
  (at level 20, n at next level, format "✓{ n }  x").

Class Valid (A : Type) := valid : A → Prop.
Hint Mode Valid ! : typeclass_instances.
Instance: Params (@valid) 2.
Notation "✓ x" := (valid x) (at level 20) : stdpp_scope.

Definition includedN `{Dist A, Op A} (n : nat) (x y : A) := ∃ z, y ≡{n}≡ x ⋅ z.
Notation "x ≼{ n } y" := (includedN n x y)
  (at level 70, n at next level, format "x  ≼{ n }  y") : stdpp_scope.
Instance: Params (@includedN) 4.
Hint Extern 0 (_ ≼{_} _) => reflexivity.

Section mixin.
  Local Set Primitive Projections.
  Record CmraMixin A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A} := {
    (* setoids *)
    mixin_cmra_op_ne (x : A) : NonExpansive (op x);
    mixin_cmra_pcore_ne n x y cx :
      x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy;
    mixin_cmra_validN_ne n : Proper (dist n ==> impl) (validN n);
    (* valid *)
    mixin_cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x;
    mixin_cmra_validN_S n x : ✓{S n} x → ✓{n} x;
    (* monoid *)
    mixin_cmra_assoc : Assoc (≡) (⋅);
    mixin_cmra_comm : Comm (≡) (⋅);
    mixin_cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x;
    mixin_cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx;
    mixin_cmra_pcore_mono x y cx :
      x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
    mixin_cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x;
    mixin_cmra_extend n x y1 y2 :
      ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
      { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }
  }.
End mixin.

(** Bundeled version *)
Structure cmraT := CmraT' {
  cmra_car :> Type;
  cmra_equiv : Equiv cmra_car;
  cmra_dist : Dist cmra_car;
  cmra_pcore : PCore cmra_car;
  cmra_op : Op cmra_car;
  cmra_valid : Valid cmra_car;
  cmra_validN : ValidN cmra_car;
  cmra_ofe_mixin : OfeMixin cmra_car;
  cmra_mixin : CmraMixin cmra_car;
  _ : Type
}.
Arguments CmraT' _ {_ _ _ _ _ _} _ _ _.
(* Given [m : CmraMixin A], the notation [CmraT A m] provides a smart
constructor, which uses [ofe_mixin_of A] to infer the canonical OFE mixin of
the type [A], so that it does not have to be given manually. *)
Notation CmraT A m := (CmraT' A (ofe_mixin_of A%type) m A) (only parsing).

Arguments cmra_car : simpl never.
Arguments cmra_equiv : simpl never.
Arguments cmra_dist : simpl never.
Arguments cmra_pcore : simpl never.
Arguments cmra_op : simpl never.
Arguments cmra_valid : simpl never.
Arguments cmra_validN : simpl never.
Arguments cmra_ofe_mixin : simpl never.
Arguments cmra_mixin : simpl never.
Add Printing Constructor cmraT.
Hint Extern 0 (PCore _) => eapply (@cmra_pcore _) : typeclass_instances.
Hint Extern 0 (Op _) => eapply (@cmra_op _) : typeclass_instances.
Hint Extern 0 (Valid _) => eapply (@cmra_valid _) : typeclass_instances.
Hint Extern 0 (ValidN _) => eapply (@cmra_validN _) : typeclass_instances.
Coercion cmra_ofeC (A : cmraT) : ofeT := OfeT A (cmra_ofe_mixin A).
Canonical Structure cmra_ofeC.

Definition cmra_mixin_of' A {Ac : cmraT} (f : Ac → A) : CmraMixin Ac := cmra_mixin Ac.
Notation cmra_mixin_of A :=
  ltac:(let H := eval hnf in (cmra_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section cmra_mixin.
  Context {A : cmraT}.
  Implicit Types x y : A.
  Global Instance cmra_op_ne (x : A) : NonExpansive (op x).
  Proof. apply (mixin_cmra_op_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_ne n x y cx :
    x ≡{n}≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡{n}≡ cy.
  Proof. apply (mixin_cmra_pcore_ne _ (cmra_mixin A)). Qed.
  Global Instance cmra_validN_ne n : Proper (dist n ==> impl) (@validN A _ n).
  Proof. apply (mixin_cmra_validN_ne _ (cmra_mixin A)). Qed.
  Lemma cmra_valid_validN x : ✓ x ↔ ∀ n, ✓{n} x.
  Proof. apply (mixin_cmra_valid_validN _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_S n x : ✓{S n} x → ✓{n} x.
  Proof. apply (mixin_cmra_validN_S _ (cmra_mixin A)). Qed.
  Global Instance cmra_assoc : Assoc (≡) (@op A _).
  Proof. apply (mixin_cmra_assoc _ (cmra_mixin A)). Qed.
  Global Instance cmra_comm : Comm (≡) (@op A _).
  Proof. apply (mixin_cmra_comm _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x.
  Proof. apply (mixin_cmra_pcore_l _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx.
  Proof. apply (mixin_cmra_pcore_idemp _ (cmra_mixin A)). Qed.
  Lemma cmra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
  Proof. apply (mixin_cmra_pcore_mono _ (cmra_mixin A)). Qed.
  Lemma cmra_validN_op_l n x y : ✓{n} (x ⋅ y) → ✓{n} x.
  Proof. apply (mixin_cmra_validN_op_l _ (cmra_mixin A)). Qed.
  Lemma cmra_extend n x y1 y2 :
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }.
  Proof. apply (mixin_cmra_extend _ (cmra_mixin A)). Qed.
End cmra_mixin.

Definition opM {A : cmraT} (x : A) (my : option A) :=
  match my with Some y => x ⋅ y | None => x end.
Infix "⋅?" := opM (at level 50, left associativity) : stdpp_scope.

(** * CoreId elements *)
Class CoreId {A : cmraT} (x : A) := core_id : pcore x ≡ Some x.
Arguments core_id {_} _ {_}.
Hint Mode CoreId + ! : typeclass_instances.
Instance: Params (@CoreId) 1.

(** * Exclusive elements (i.e., elements that cannot have a frame). *)
Class Exclusive {A : cmraT} (x : A) := exclusive0_l y : ✓{0} (x ⋅ y) → False.
Arguments exclusive0_l {_} _ {_} _ _.
Hint Mode Exclusive + ! : typeclass_instances.
Instance: Params (@Exclusive) 1.

(** * Cancelable elements. *)
Class Cancelable {A : cmraT} (x : A) :=
  cancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ≡{n}≡ z.
Arguments cancelableN {_} _ {_} _ _ _ _.
Hint Mode Cancelable + ! : typeclass_instances.
Instance: Params (@Cancelable) 1.

(** * Identity-free elements. *)
Class IdFree {A : cmraT} (x : A) :=
  id_free0_r y : ✓{0}x → x ⋅ y ≡{0}≡ x → False.
Arguments id_free0_r {_} _ {_} _ _.
Hint Mode IdFree + ! : typeclass_instances.
Instance: Params (@IdFree) 1.

(** * CMRAs whose core is total *)
(** The function [core] may return a dummy when used on CMRAs without total
core. *)
Class CmraTotal (A : cmraT) := cmra_total (x : A) : is_Some (pcore x).
Hint Mode CmraTotal ! : typeclass_instances.

Class Core (A : Type) := core : A → A.
Hint Mode Core ! : typeclass_instances.
Instance: Params (@core) 2.

Instance core' `{PCore A} : Core A := λ x, from_option id x (pcore x).
Arguments core' _ _ _ /.

(** * CMRAs with a unit element *)
Class Unit (A : Type) := ε : A.
Arguments ε {_ _}.

Record UcmraMixin A `{Dist A, Equiv A, PCore A, Op A, Valid A, Unit A} := {
  mixin_ucmra_unit_valid : ✓ ε;
  mixin_ucmra_unit_left_id : LeftId (≡) ε (⋅);
  mixin_ucmra_pcore_unit : pcore ε ≡ Some ε
}.

Structure ucmraT := UcmraT' {
  ucmra_car :> Type;
  ucmra_equiv : Equiv ucmra_car;
  ucmra_dist : Dist ucmra_car;
  ucmra_pcore : PCore ucmra_car;
  ucmra_op : Op ucmra_car;
  ucmra_valid : Valid ucmra_car;
  ucmra_validN : ValidN ucmra_car;
  ucmra_unit : Unit ucmra_car;
  ucmra_ofe_mixin : OfeMixin ucmra_car;
  ucmra_cmra_mixin : CmraMixin ucmra_car;
  ucmra_mixin : UcmraMixin ucmra_car;
  _ : Type;
}.
Arguments UcmraT' _ {_ _ _ _ _ _ _} _ _ _ _.
Notation UcmraT A m :=
  (UcmraT' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) m A) (only parsing).
Arguments ucmra_car : simpl never.
Arguments ucmra_equiv : simpl never.
Arguments ucmra_dist : simpl never.
Arguments ucmra_pcore : simpl never.
Arguments ucmra_op : simpl never.
Arguments ucmra_valid : simpl never.
Arguments ucmra_validN : simpl never.
Arguments ucmra_ofe_mixin : simpl never.
Arguments ucmra_cmra_mixin : simpl never.
Arguments ucmra_mixin : simpl never.
Add Printing Constructor ucmraT.
Hint Extern 0 (Unit _) => eapply (@ucmra_unit _) : typeclass_instances.
Coercion ucmra_ofeC (A : ucmraT) : ofeT := OfeT A (ucmra_ofe_mixin A).
Canonical Structure ucmra_ofeC.
Coercion ucmra_cmraR (A : ucmraT) : cmraT :=
  CmraT' A (ucmra_ofe_mixin A) (ucmra_cmra_mixin A) A.
Canonical Structure ucmra_cmraR.

(** Lifting properties from the mixin *)
Section ucmra_mixin.
  Context {A : ucmraT}.
  Implicit Types x y : A.
  Lemma ucmra_unit_valid : ✓ (ε : A).
  Proof. apply (mixin_ucmra_unit_valid _ (ucmra_mixin A)). Qed.
  Global Instance ucmra_unit_left_id : LeftId (≡) ε (@op A _).
  Proof. apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A)). Qed.
  Lemma ucmra_pcore_unit : pcore (ε:A) ≡ Some ε.
  Proof. apply (mixin_ucmra_pcore_unit _ (ucmra_mixin A)). Qed.
End ucmra_mixin.

(** * Discrete CMRAs *)
Class CmraDiscrete (A : cmraT) := {
  cmra_discrete_ofe_discrete :> OfeDiscrete A;
  cmra_discrete_valid (x : A) : ✓{0} x → ✓ x
}.
Hint Mode CmraDiscrete ! : typeclass_instances.

(** * Morphisms *)
Class CmraMorphism {A B : cmraT} (f : A → B) := {
  cmra_morphism_ne :> NonExpansive f;
  cmra_morphism_validN n x : ✓{n} x → ✓{n} f x;
  cmra_morphism_pcore x : pcore (f x) ≡ f <$> pcore x;
  cmra_morphism_op x y : f x ⋅ f y ≡ f (x ⋅ y)
}.
Arguments cmra_morphism_validN {_ _} _ {_} _ _ _.
Arguments cmra_morphism_pcore {_ _} _ {_} _.
Arguments cmra_morphism_op {_ _} _ {_} _ _.

(** * Properties **)
Section cmra.
Context {A : cmraT}.
Implicit Types x y z : A.
Implicit Types xs ys zs : list A.

(** ** Setoids *)
Global Instance cmra_pcore_ne' : NonExpansive (@pcore A _).
Proof.
  intros n x y Hxy. destruct (pcore x) as [cx|] eqn:?.
  { destruct (cmra_pcore_ne n x y cx) as (cy&->&->); auto. }
  destruct (pcore y) as [cy|] eqn:?; auto.
  destruct (cmra_pcore_ne n y x cy) as (cx&?&->); simplify_eq/=; auto.
Qed.
Lemma cmra_pcore_proper x y cx :
  x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy.
Proof.
  intros. destruct (cmra_pcore_ne 0 x y cx) as (cy&?&?); auto.
  exists cy; split; [done|apply equiv_dist=> n].
  destruct (cmra_pcore_ne n x y cx) as (cy'&?&?); naive_solver.
Qed.
Global Instance cmra_pcore_proper' : Proper ((≡) ==> (≡)) (@pcore A _).
Proof. apply (ne_proper _). Qed.
Global Instance cmra_op_ne' : NonExpansive2 (@op A _).
Proof. intros n x1 x2 Hx y1 y2 Hy. by rewrite Hy (comm _ x1) Hx (comm _ y2). Qed.
Global Instance cmra_op_proper' : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
Proof. apply (ne_proper_2 _). Qed.
Global Instance cmra_validN_ne' : Proper (dist n ==> iff) (@validN A _ n) | 1.
Proof. by split; apply cmra_validN_ne. Qed.
Global Instance cmra_validN_proper : Proper ((≡) ==> iff) (@validN A _ n) | 1.
Proof. by intros n x1 x2 Hx; apply cmra_validN_ne', equiv_dist. Qed.

Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (@valid A _).
Proof.
  intros x y Hxy; rewrite !cmra_valid_validN.
  by split=> ? n; [rewrite -Hxy|rewrite Hxy].
Qed.
Global Instance cmra_includedN_ne n :
  Proper (dist n ==> dist n ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_includedN_proper n :
  Proper ((≡) ==> (≡) ==> iff) (@includedN A _ _ n) | 1.
Proof.
  intros x x' Hx y y' Hy; revert Hx Hy; rewrite !equiv_dist=> Hx Hy.
  by rewrite (Hx n) (Hy n).
Qed.
Global Instance cmra_included_proper :
  Proper ((≡) ==> (≡) ==> iff) (@included A _ _) | 1.
Proof.
  intros x x' Hx y y' Hy.
  by split; intros [z ?]; exists z; [rewrite -Hx -Hy|rewrite Hx Hy].
Qed.
Global Instance cmra_opM_ne : NonExpansive2 (@opM A).
Proof. destruct 2; by ofe_subst. Qed.
Global Instance cmra_opM_proper : Proper ((≡) ==> (≡) ==> (≡)) (@opM A).
Proof. destruct 2; by setoid_subst. Qed.

Global Instance CoreId_proper : Proper ((≡) ==> iff) (@CoreId A).
Proof. solve_proper. Qed.
Global Instance Exclusive_proper : Proper ((≡) ==> iff) (@Exclusive A).
Proof. intros x y Hxy. rewrite /Exclusive. by setoid_rewrite Hxy. Qed.
Global Instance Cancelable_proper : Proper ((≡) ==> iff) (@Cancelable A).
Proof. intros x y Hxy. rewrite /Cancelable. by setoid_rewrite Hxy. Qed.
Global Instance IdFree_proper : Proper ((≡) ==> iff) (@IdFree A).
Proof. intros x y Hxy. rewrite /IdFree. by setoid_rewrite Hxy. Qed.

(** ** Op *)
Lemma cmra_opM_assoc x y mz : (x ⋅ y) ⋅? mz ≡ x ⋅ (y ⋅? mz).
Proof. destruct mz; by rewrite /= -?assoc. Qed.

(** ** Validity *)
Lemma cmra_validN_le n n' x : ✓{n} x → n' ≤ n → ✓{n'} x.
Proof. induction 2; eauto using cmra_validN_S. Qed.
Lemma cmra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_op_r n x y : ✓{n} (x ⋅ y) → ✓{n} y.
Proof. rewrite (comm _ x); apply cmra_validN_op_l. Qed.
Lemma cmra_valid_op_r x y : ✓ (x ⋅ y) → ✓ y.
Proof. rewrite !cmra_valid_validN; eauto using cmra_validN_op_r. Qed.

(** ** Core *)
Lemma cmra_pcore_l' x cx : pcore x ≡ Some cx → cx ⋅ x ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r x cx : pcore x = Some cx → x ⋅ cx ≡ x.
Proof. intros. rewrite comm. by apply cmra_pcore_l. Qed.
Lemma cmra_pcore_r' x cx : pcore x ≡ Some cx → x ⋅ cx ≡ x.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. by apply cmra_pcore_r. Qed.
Lemma cmra_pcore_idemp' x cx : pcore x ≡ Some cx → pcore cx ≡ Some cx.
Proof. intros (cx'&?&->)%equiv_Some_inv_r'. eauto using cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup x cx : pcore x = Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp. Qed.
Lemma cmra_pcore_dup' x cx : pcore x ≡ Some cx → cx ≡ cx ⋅ cx.
Proof. intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp'. Qed.
Lemma cmra_pcore_validN n x cx : ✓{n} x → pcore x = Some cx → ✓{n} cx.
Proof.
  intros Hvx Hx%cmra_pcore_l. move: Hvx; rewrite -Hx. apply cmra_validN_op_l.
Qed.
Lemma cmra_pcore_valid x cx : ✓ x → pcore x = Some cx → ✓ cx.
Proof.
  intros Hv Hx%cmra_pcore_l. move: Hv; rewrite -Hx. apply cmra_valid_op_l.
Qed.

(** ** CoreId elements *)
Lemma core_id_dup x `{!CoreId x} : x ≡ x ⋅ x.
Proof. by apply cmra_pcore_dup' with x. Qed.

(** ** Exclusive elements *)
Lemma exclusiveN_l n x `{!Exclusive x} y : ✓{n} (x ⋅ y) → False.
Proof. intros. eapply (exclusive0_l x y), cmra_validN_le; eauto with lia. Qed.
Lemma exclusiveN_r n x `{!Exclusive x} y : ✓{n} (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusiveN_l. Qed.
Lemma exclusive_l x `{!Exclusive x} y : ✓ (x ⋅ y) → False.
Proof. by move /cmra_valid_validN /(_ 0) /exclusive0_l. Qed.
Lemma exclusive_r x `{!Exclusive x} y : ✓ (y ⋅ x) → False.
Proof. rewrite comm. by apply exclusive_l. Qed.
Lemma exclusiveN_opM n x `{!Exclusive x} my : ✓{n} (x ⋅? my) → my = None.
Proof. destruct my as [y|]. move=> /(exclusiveN_l _ x) []. done. Qed.
Lemma exclusive_includedN n x `{!Exclusive x} y : x ≼{n} y → ✓{n} y → False.
Proof. intros [? ->]. by apply exclusiveN_l. Qed.
Lemma exclusive_included x `{!Exclusive x} y : x ≼ y → ✓ y → False.
Proof. intros [? ->]. by apply exclusive_l. Qed.

(** ** Order *)
Lemma cmra_included_includedN n x y : x ≼ y → x ≼{n} y.
Proof. intros [z ->]. by exists z. Qed.
Global Instance cmra_includedN_trans n : Transitive (@includedN A _ _ n).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Global Instance cmra_included_trans: Transitive (@included A _ _).
Proof.
  intros x y z [z1 Hy] [z2 Hz]; exists (z1 ⋅ z2). by rewrite assoc -Hy -Hz.
Qed.
Lemma cmra_valid_included x y : ✓ y → x ≼ y → ✓ x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_valid_op_l. Qed.
Lemma cmra_validN_includedN n x y : ✓{n} y → x ≼{n} y → ✓{n} x.
Proof. intros Hyv [z ?]; ofe_subst y; eauto using cmra_validN_op_l. Qed.
Lemma cmra_validN_included n x y : ✓{n} y → x ≼ y → ✓{n} x.
Proof. intros Hyv [z ?]; setoid_subst; eauto using cmra_validN_op_l. Qed.

Lemma cmra_includedN_S n x y : x ≼{S n} y → x ≼{n} y.
Proof. by intros [z Hz]; exists z; apply dist_S. Qed.
Lemma cmra_includedN_le n n' x y : x ≼{n} y → n' ≤ n → x ≼{n'} y.
Proof. induction 2; auto using cmra_includedN_S. Qed.

Lemma cmra_includedN_l n x y : x ≼{n} x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_included_l x y : x ≼ x ⋅ y.
Proof. by exists y. Qed.
Lemma cmra_includedN_r n x y : y ≼{n} x ⋅ y.
Proof. rewrite (comm op); apply cmra_includedN_l. Qed.
Lemma cmra_included_r x y : y ≼ x ⋅ y.
Proof. rewrite (comm op); apply cmra_included_l. Qed.

Lemma cmra_pcore_mono' x y cx :
  x ≼ y → pcore x ≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy.
Proof.
  intros ? (cx'&?&Hcx)%equiv_Some_inv_r'.
  destruct (cmra_pcore_mono x y cx') as (cy&->&?); auto.
  exists cy; by rewrite Hcx.
Qed.
Lemma cmra_pcore_monoN' n x y cx :
  x ≼{n} y → pcore x ≡{n}≡ Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼{n} cy.
Proof.
  intros [z Hy] (cx'&?&Hcx)%dist_Some_inv_r'.
  destruct (cmra_pcore_mono x (x ⋅ z) cx')
    as (cy&Hxy&?); auto using cmra_included_l.
  assert (pcore y ≡{n}≡ Some cy) as (cy'&?&Hcy')%dist_Some_inv_r'.
  { by rewrite Hy Hxy. }
  exists cy'; split; first done.
  rewrite Hcx -Hcy'; auto using cmra_included_includedN.
Qed.
Lemma cmra_included_pcore x cx : pcore x = Some cx → cx ≼ x.
Proof. exists x. by rewrite cmra_pcore_l. Qed.

Lemma cmra_monoN_l n x y z : x ≼{n} y → z ⋅ x ≼{n} z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_mono_l x y z : x ≼ y → z ⋅ x ≼ z ⋅ y.
Proof. by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op). Qed.
Lemma cmra_monoN_r n x y z : x ≼{n} y → x ⋅ z ≼{n} y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_monoN_l. Qed.
Lemma cmra_mono_r x y z : x ≼ y → x ⋅ z ≼ y ⋅ z.
Proof. by intros; rewrite -!(comm _ z); apply cmra_mono_l. Qed.
Lemma cmra_monoN n x1 x2 y1 y2 : x1 ≼{n} y1 → x2 ≼{n} y2 → x1 ⋅ x2 ≼{n} y1 ⋅ y2.
Proof. intros; etrans; eauto using cmra_monoN_l, cmra_monoN_r. Qed.
Lemma cmra_mono x1 x2 y1 y2 : x1 ≼ y1 → x2 ≼ y2 → x1 ⋅ x2 ≼ y1 ⋅ y2.
Proof. intros; etrans; eauto using cmra_mono_l, cmra_mono_r. Qed.

Global Instance cmra_monoN' n :
  Proper (includedN n ==> includedN n ==> includedN n) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_monoN. Qed.
Global Instance cmra_mono' :
  Proper (included ==> included ==> included) (@op A _).
Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_mono. Qed.

Lemma cmra_included_dist_l n x1 x2 x1' :
  x1 ≼ x2 → x1' ≡{n}≡ x1 → ∃ x2', x1' ≼ x2' ∧ x2' ≡{n}≡ x2.
Proof.
  intros [z Hx2] Hx1; exists (x1' ⋅ z); split; auto using cmra_included_l.
  by rewrite Hx1 Hx2.
Qed.

(** ** Total core *)
Section total_core.
  Local Set Default Proof Using "Type*".
  Context `{CmraTotal A}.

  Lemma cmra_core_l x : core x ⋅ x ≡ x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_l.
  Qed.
  Lemma cmra_core_idemp x : core (core x) ≡ core x.
  Proof.
    destruct (cmra_total x) as [cx Hcx]. by rewrite /core /= Hcx cmra_pcore_idemp.
  Qed.
  Lemma cmra_core_mono x y : x ≼ y → core x ≼ core y.
  Proof.
    intros; destruct (cmra_total x) as [cx Hcx].
    destruct (cmra_pcore_mono x y cx) as (cy&Hcy&?); auto.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Global Instance cmra_core_ne : NonExpansive (@core A _).
  Proof.
    intros n x y Hxy. destruct (cmra_total x) as [cx Hcx].
    by rewrite /core /= -Hxy Hcx.
  Qed.
  Global Instance cmra_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (ne_proper _). Qed.

  Lemma cmra_core_r x : x ⋅ core x ≡ x.
  Proof. by rewrite (comm _ x) cmra_core_l. Qed.
  Lemma cmra_core_dup x : core x ≡ core x ⋅ core x.
  Proof. by rewrite -{3}(cmra_core_idemp x) cmra_core_r. Qed.
  Lemma cmra_core_validN n x : ✓{n} x → ✓{n} core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_validN_op_l. Qed.
  Lemma cmra_core_valid x : ✓ x → ✓ core x.
  Proof. rewrite -{1}(cmra_core_l x); apply cmra_valid_op_l. Qed.

  Lemma core_id_total x : CoreId x ↔ core x ≡ x.
  Proof.
    split; [intros; by rewrite /core /= (core_id x)|].
    rewrite /CoreId /core /=.
    destruct (cmra_total x) as [? ->]. by constructor.
  Qed.
  Lemma core_id_core x `{!CoreId x} : core x ≡ x.
  Proof. by apply core_id_total. Qed.

  Global Instance cmra_core_core_id x : CoreId (core x).
  Proof.
    destruct (cmra_total x) as [cx Hcx].
    rewrite /CoreId /core /= Hcx /=. eauto using cmra_pcore_idemp.
  Qed.

  Lemma cmra_included_core x : core x ≼ x.
  Proof. by exists x; rewrite cmra_core_l. Qed.
  Global Instance cmra_includedN_preorder n : PreOrder (@includedN A _ _ n).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Global Instance cmra_included_preorder : PreOrder (@included A _ _).
  Proof.
    split; [|apply _]. by intros x; exists (core x); rewrite cmra_core_r.
  Qed.
  Lemma cmra_core_monoN n x y : x ≼{n} y → core x ≼{n} core y.
  Proof.
    intros [z ->].
    apply cmra_included_includedN, cmra_core_mono, cmra_included_l.
  Qed.
End total_core.

(** ** Discrete *)
Lemma cmra_discrete_included_l x y : Discrete x → ✓{0} y → x ≼{0} y → x ≼ y.
Proof.
  intros ?? [x' ?].
  destruct (cmra_extend 0 y x x') as (z&z'&Hy&Hz&Hz'); auto; simpl in *.
  by exists z'; rewrite Hy (discrete x z).
Qed.
Lemma cmra_discrete_included_r x y : Discrete y → x ≼{0} y → x ≼ y.
Proof. intros ? [x' ?]. exists x'. by apply (discrete y). Qed.
Lemma cmra_op_discrete x1 x2 :
  ✓ (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *.
  { rewrite -?Hz. by apply cmra_valid_validN. }
  by rewrite Hz' (discrete x1 y1) // (discrete x2 y2).
Qed.

(** ** Discrete *)
Lemma cmra_discrete_valid_iff `{CmraDiscrete A} n x : ✓ x ↔ ✓{n} x.
Proof.
  split; first by rewrite cmra_valid_validN.
  eauto using cmra_discrete_valid, cmra_validN_le with lia.
Qed.
Lemma cmra_discrete_valid_iff_0 `{CmraDiscrete A} n x : ✓{0} x ↔ ✓{n} x.
Proof. by rewrite -!cmra_discrete_valid_iff. Qed.
Lemma cmra_discrete_included_iff `{OfeDiscrete A} n x y : x ≼ y ↔ x ≼{n} y.
Proof.
  split; first by apply cmra_included_includedN.
  intros [z ->%(discrete_iff _ _)]; eauto using cmra_included_l.
Qed.
Lemma cmra_discrete_included_iff_0 `{OfeDiscrete A} n x y : x ≼{0} y ↔ x ≼{n} y.
Proof. by rewrite -!cmra_discrete_included_iff. Qed.

(** Cancelable elements  *)
Global Instance cancelable_proper : Proper (equiv ==> iff) (@Cancelable A).
Proof. unfold Cancelable. intros x x' EQ. by setoid_rewrite EQ. Qed.
Lemma cancelable x `{!Cancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z.
Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (cancelableN x). Qed.
Lemma discrete_cancelable x `{CmraDiscrete A}:
  (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ≡ z) → Cancelable x.
Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed.
Global Instance cancelable_op x y :
  Cancelable x → Cancelable y → Cancelable (x ⋅ y).
Proof.
  intros ?? n z z' ??. apply (cancelableN y), (cancelableN x).
  - eapply cmra_validN_op_r. by rewrite assoc.
  - by rewrite assoc.
  - by rewrite !assoc.
Qed.
Global Instance exclusive_cancelable (x : A) : Exclusive x → Cancelable x.
Proof. intros ? n z z' []%(exclusiveN_l _ x). Qed.

(** Id-free elements  *)
Global Instance id_free_ne n : Proper (dist n ==> iff) (@IdFree A).
Proof.
  intros x x' EQ%(dist_le _ 0); last lia. rewrite /IdFree.
  split=> y ?; (rewrite -EQ || rewrite EQ); eauto.
Qed.
Global Instance id_free_proper : Proper (equiv ==> iff) (@IdFree A).
Proof. by move=> P Q /equiv_dist /(_ 0)=> ->. Qed.
Lemma id_freeN_r n n' x `{!IdFree x} y : ✓{n}x → x ⋅ y ≡{n'}≡ x → False.
Proof. eauto using cmra_validN_le, dist_le with lia. Qed.
Lemma id_freeN_l n n' x `{!IdFree x} y : ✓{n}x → y ⋅ x ≡{n'}≡ x → False.
Proof. rewrite comm. eauto using id_freeN_r. Qed.
Lemma id_free_r x `{!IdFree x} y : ✓x → x ⋅ y ≡ x → False.
Proof. move=> /cmra_valid_validN ? /equiv_dist. eauto. Qed.
Lemma id_free_l x `{!IdFree x} y : ✓x → y ⋅ x ≡ x → False.
Proof. rewrite comm. eauto using id_free_r. Qed.
Lemma discrete_id_free x `{CmraDiscrete A}:
  (∀ y, ✓ x → x ⋅ y ≡ x → False) → IdFree x.
Proof.
  intros Hx y ??. apply (Hx y), (discrete _); eauto using cmra_discrete_valid.
Qed.
Global Instance id_free_op_r x y : IdFree y → Cancelable x → IdFree (x ⋅ y).
Proof.
  intros ?? z ? Hid%symmetry. revert Hid. rewrite -assoc=>/(cancelableN x) ?.
  eapply (id_free0_r _); [by eapply cmra_validN_op_r |symmetry; eauto].
Qed.
Global Instance id_free_op_l x y : IdFree x → Cancelable y → IdFree (x ⋅ y).
Proof. intros. rewrite comm. apply _. Qed.
Global Instance exclusive_id_free x : Exclusive x → IdFree x.
Proof. intros ? z ? Hid. apply (exclusiveN_l 0 x z). by rewrite Hid. Qed.
End cmra.

(** * Properties about CMRAs with a unit element **)
Section ucmra.
  Context {A : ucmraT}.
  Implicit Types x y z : A.

  Lemma ucmra_unit_validN n : ✓{n} (ε:A).
  Proof. apply cmra_valid_validN, ucmra_unit_valid. Qed.
  Lemma ucmra_unit_leastN n x : ε ≼{n} x.
  Proof. by exists x; rewrite left_id. Qed.
  Lemma ucmra_unit_least x : ε ≼ x.
  Proof. by exists x; rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id : RightId (≡) ε (@op A _).
  Proof. by intros x; rewrite (comm op) left_id. Qed.
  Global Instance ucmra_unit_core_id : CoreId (ε:A).
  Proof. apply ucmra_pcore_unit. Qed.

  Global Instance cmra_unit_cmra_total : CmraTotal A.
  Proof.
    intros x. destruct (cmra_pcore_mono' ε x ε) as (cx&->&?);
      eauto using ucmra_unit_least, (core_id (ε:A)).
  Qed.
  Global Instance empty_cancelable : Cancelable (ε:A).
  Proof. intros ???. by rewrite !left_id. Qed.

  (* For big ops *)
  Global Instance cmra_monoid : Monoid (@op A _) := {| monoid_unit := ε |}.
End ucmra.

Hint Immediate cmra_unit_cmra_total.

(** * Properties about CMRAs with Leibniz equality *)
Section cmra_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : cmraT} `{!LeibnizEquiv A}.
  Implicit Types x y : A.

  Global Instance cmra_assoc_L : Assoc (=) (@op A _).
  Proof. intros x y z. unfold_leibniz. by rewrite assoc. Qed.
  Global Instance cmra_comm_L : Comm (=) (@op A _).
  Proof. intros x y. unfold_leibniz. by rewrite comm. Qed.

  Lemma cmra_pcore_l_L x cx : pcore x = Some cx → cx ⋅ x = x.
  Proof. unfold_leibniz. apply cmra_pcore_l'. Qed.
  Lemma cmra_pcore_idemp_L x cx : pcore x = Some cx → pcore cx = Some cx.
  Proof. unfold_leibniz. apply cmra_pcore_idemp'. Qed.

  Lemma cmra_opM_assoc_L x y mz : (x ⋅ y) ⋅? mz = x ⋅ (y ⋅? mz).
  Proof. unfold_leibniz. apply cmra_opM_assoc. Qed.

  (** ** Core *)
  Lemma cmra_pcore_r_L x cx : pcore x = Some cx → x ⋅ cx = x.
  Proof. unfold_leibniz. apply cmra_pcore_r'. Qed.
  Lemma cmra_pcore_dup_L x cx : pcore x = Some cx → cx = cx ⋅ cx.
  Proof. unfold_leibniz. apply cmra_pcore_dup'. Qed.

  (** ** CoreId elements *)
  Lemma core_id_dup_L x `{!CoreId x} : x = x ⋅ x.
  Proof. unfold_leibniz. by apply core_id_dup. Qed.

  (** ** Total core *)
  Section total_core.
    Context `{CmraTotal A}.

    Lemma cmra_core_r_L x : x ⋅ core x = x.
    Proof. unfold_leibniz. apply cmra_core_r. Qed.
    Lemma cmra_core_l_L x : core x ⋅ x = x.
    Proof. unfold_leibniz. apply cmra_core_l. Qed.
    Lemma cmra_core_idemp_L x : core (core x) = core x.
    Proof. unfold_leibniz. apply cmra_core_idemp. Qed.
    Lemma cmra_core_dup_L x : core x = core x ⋅ core x.
    Proof. unfold_leibniz. apply cmra_core_dup. Qed.
    Lemma core_id_total_L x : CoreId x ↔ core x = x.
    Proof. unfold_leibniz. apply core_id_total. Qed.
    Lemma core_id_core_L x `{!CoreId x} : core x = x.
    Proof. by apply core_id_total_L. Qed.
  End total_core.
End cmra_leibniz.

Section ucmra_leibniz.
  Local Set Default Proof Using "Type*".
  Context {A : ucmraT} `{!LeibnizEquiv A}.
  Implicit Types x y z : A.

  Global Instance ucmra_unit_left_id_L : LeftId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite left_id. Qed.
  Global Instance ucmra_unit_right_id_L : RightId (=) ε (@op A _).
  Proof. intros x. unfold_leibniz. by rewrite right_id. Qed.
End ucmra_leibniz.

(** * Constructing a CMRA with total core *)
Section cmra_total.
  Context A `{Dist A, Equiv A, PCore A, Op A, Valid A, ValidN A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_ne : ∀ x : A, NonExpansive (op x)).
  Context (core_ne : NonExpansive (@core A _)).
  Context (validN_ne : ∀ n, Proper (dist n ==> impl) (@validN A _ n)).
  Context (valid_validN : ∀ (x : A), ✓ x ↔ ∀ n, ✓{n} x).
  Context (validN_S : ∀ n (x : A), ✓{S n} x → ✓{n} x).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (validN_op_l : ∀ n (x y : A), ✓{n} (x ⋅ y) → ✓{n} x).
  Context (extend : ∀ n (x y1 y2 : A),
    ✓{n} x → x ≡{n}≡ y1 ⋅ y2 →
    { z1 : A & { z2 | x ≡ z1 ⋅ z2 ∧ z1 ≡{n}≡ y1 ∧ z2 ≡{n}≡ y2 } }).
  Lemma cmra_total_mixin : CmraMixin A.
  Proof using Type*.
    split; auto.
    - intros n x y ? Hcx%core_ne Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End cmra_total.

(** * Properties about morphisms *)
Instance cmra_morphism_id {A : cmraT} : CmraMorphism (@id A).
Proof. split=>//=. apply _. intros. by rewrite option_fmap_id. Qed.
Instance cmra_morphism_proper {A B : cmraT} (f : A → B) `{!CmraMorphism f} :
  Proper ((≡) ==> (≡)) f := ne_proper _.
Instance cmra_morphism_compose {A B C : cmraT} (f : A → B) (g : B → C) :
  CmraMorphism f → CmraMorphism g → CmraMorphism (g ∘ f).
Proof.
  split.
  - apply _.
  - move=> n x Hx /=. by apply cmra_morphism_validN, cmra_morphism_validN.
  - move=> x /=. by rewrite 2!cmra_morphism_pcore option_fmap_compose.
  - move=> x y /=. by rewrite !cmra_morphism_op.
Qed.

Section cmra_morphism.
  Local Set Default Proof Using "Type*".
  Context {A B : cmraT} (f : A → B) `{!CmraMorphism f}.
  Lemma cmra_morphism_core x : core (f x) ≡ f (core x).
  Proof. unfold core, core'. rewrite cmra_morphism_pcore. by destruct (pcore x). Qed.
  Lemma cmra_morphism_monotone x y : x ≼ y → f x ≼ f y.
  Proof. intros [z ->]. exists (f z). by rewrite cmra_morphism_op. Qed.
  Lemma cmra_morphism_monotoneN n x y : x ≼{n} y → f x ≼{n} f y.
  Proof. intros [z ->]. exists (f z). by rewrite cmra_morphism_op. Qed.
  Lemma cmra_monotone_valid x : ✓ x → ✓ f x.
  Proof. rewrite !cmra_valid_validN; eauto using cmra_morphism_validN. Qed.
End cmra_morphism.

(** Functors *)
Structure rFunctor := RFunctor {
  rFunctor_car : ofeT → ofeT → cmraT;
  rFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → rFunctor_car A1 B1 -n> rFunctor_car A2 B2;
  rFunctor_ne A1 A2 B1 B2 :
    NonExpansive (@rFunctor_map A1 A2 B1 B2);
  rFunctor_id {A B} (x : rFunctor_car A B) : rFunctor_map (cid,cid) x ≡ x;
  rFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    rFunctor_map (f◎g, g'◎f') x ≡ rFunctor_map (g,g') (rFunctor_map (f,f') x);
  rFunctor_mor {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (rFunctor_map fg)
}.
Existing Instances rFunctor_ne rFunctor_mor.
Instance: Params (@rFunctor_map) 5.

Delimit Scope rFunctor_scope with RF.
Bind Scope rFunctor_scope with rFunctor.

Class rFunctorContractive (F : rFunctor) :=
  rFunctor_contractive A1 A2 B1 B2 :> Contractive (@rFunctor_map F A1 A2 B1 B2).

Definition rFunctor_diag (F: rFunctor) (A: ofeT) : cmraT := rFunctor_car F A A.
Coercion rFunctor_diag : rFunctor >-> Funclass.

Program Definition constRF (B : cmraT) : rFunctor :=
  {| rFunctor_car A1 A2 := B; rFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constRF : cmraT >-> rFunctor.

Instance constRF_contractive B : rFunctorContractive (constRF B).
Proof. rewrite /rFunctorContractive; apply _. Qed.

Structure urFunctor := URFunctor {
  urFunctor_car : ofeT → ofeT → ucmraT;
  urFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → urFunctor_car A1 B1 -n> urFunctor_car A2 B2;
  urFunctor_ne A1 A2 B1 B2 :
    NonExpansive (@urFunctor_map A1 A2 B1 B2);
  urFunctor_id {A B} (x : urFunctor_car A B) : urFunctor_map (cid,cid) x ≡ x;
  urFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    urFunctor_map (f◎g, g'◎f') x ≡ urFunctor_map (g,g') (urFunctor_map (f,f') x);
  urFunctor_mor {A1 A2 B1 B2} (fg : (A2 -n> A1) * (B1 -n> B2)) :
    CmraMorphism (urFunctor_map fg)
}.
Existing Instances urFunctor_ne urFunctor_mor.
Instance: Params (@urFunctor_map) 5.

Delimit Scope urFunctor_scope with URF.
Bind Scope urFunctor_scope with urFunctor.

Class urFunctorContractive (F : urFunctor) :=
  urFunctor_contractive A1 A2 B1 B2 :> Contractive (@urFunctor_map F A1 A2 B1 B2).

Definition urFunctor_diag (F: urFunctor) (A: ofeT) : ucmraT := urFunctor_car F A A.
Coercion urFunctor_diag : urFunctor >-> Funclass.

Program Definition constURF (B : ucmraT) : urFunctor :=
  {| urFunctor_car A1 A2 := B; urFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constURF : ucmraT >-> urFunctor.

Instance constURF_contractive B : urFunctorContractive (constURF B).
Proof. rewrite /urFunctorContractive; apply _. Qed.

(** * Transporting a CMRA equality *)
Definition cmra_transport {A B : cmraT} (H : A = B) (x : A) : B :=
  eq_rect A id x _ H.

Section cmra_transport.
  Context {A B : cmraT} (H : A = B).
  Notation T := (cmra_transport H).
  Global Instance cmra_transport_ne : NonExpansive T.
  Proof. by intros ???; destruct H. Qed.
  Global Instance cmra_transport_proper : Proper ((≡) ==> (≡)) T.
  Proof. by intros ???; destruct H. Qed.
  Lemma cmra_transport_op x y : T (x ⋅ y) = T x ⋅ T y.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_core x : T (core x) = core (T x).
  Proof. by destruct H. Qed.
  Lemma cmra_transport_validN n x : ✓{n} T x ↔ ✓{n} x.
  Proof. by destruct H. Qed.
  Lemma cmra_transport_valid x : ✓ T x ↔ ✓ x.
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_discrete x : Discrete x → Discrete (T x).
  Proof. by destruct H. Qed.
  Global Instance cmra_transport_core_id x : CoreId x → CoreId (T x).
  Proof. by destruct H. Qed.
End cmra_transport.

(** * Instances *)
(** ** Discrete CMRA *)
Record RAMixin A `{Equiv A, PCore A, Op A, Valid A} := {
  (* setoids *)
  ra_op_proper (x : A) : Proper ((≡) ==> (≡)) (op x);
  ra_core_proper x y cx :
    x ≡ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≡ cy;
  ra_validN_proper : Proper ((≡) ==> impl) valid;
  (* monoid *)
  ra_assoc : Assoc (≡) (⋅);
  ra_comm : Comm (≡) (⋅);
  ra_pcore_l x cx : pcore x = Some cx → cx ⋅ x ≡ x;
  ra_pcore_idemp x cx : pcore x = Some cx → pcore cx ≡ Some cx;
  ra_pcore_mono x y cx :
    x ≼ y → pcore x = Some cx → ∃ cy, pcore y = Some cy ∧ cx ≼ cy;
  ra_valid_op_l x y : ✓ (x ⋅ y) → ✓ x
}.

Section discrete.
  Local Set Default Proof Using "Type*".
  Context `{Equiv A, PCore A, Op A, Valid A} (Heq : @Equivalence A (≡)).
  Context (ra_mix : RAMixin A).
  Existing Instances discrete_dist.

  Instance discrete_validN : ValidN A := λ n x, ✓ x.
  Definition discrete_cmra_mixin : CmraMixin A.
  Proof.
    destruct ra_mix; split; try done.
    - intros x; split; first done. by move=> /(_ 0).
    - intros n x y1 y2 ??; by exists y1, y2.
  Qed.

  Instance discrete_cmra_discrete :
    CmraDiscrete (CmraT' A (discrete_ofe_mixin Heq) discrete_cmra_mixin A).
  Proof. split. apply _. done. Qed.
End discrete.

(** A smart constructor for the discrete RA over a carrier [A]. It uses
[ofe_discrete_equivalence_of A] to make sure the same [Equivalence] proof is
used as when constructing the OFE. *)
Notation discreteR A ra_mix :=
  (CmraT A (discrete_cmra_mixin (discrete_ofe_equivalence_of A%type) ra_mix))
  (only parsing).

Section ra_total.
  Local Set Default Proof Using "Type*".
  Context A `{Equiv A, PCore A, Op A, Valid A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_proper : ∀ x : A, Proper ((≡) ==> (≡)) (op x)).
  Context (core_proper: Proper ((≡) ==> (≡)) (@core A _)).
  Context (valid_proper : Proper ((≡) ==> impl) (@valid A _)).
  Context (op_assoc : Assoc (≡) (@op A _)).
  Context (op_comm : Comm (≡) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x ≡ x).
  Context (core_idemp : ∀ x : A, core (core x) ≡ core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ x y : A, ✓ (x ⋅ y) → ✓ x).
  Lemma ra_total_mixin : RAMixin A.
  Proof.
    split; auto.
    - intros x y ? Hcx%core_proper Hx; move: Hcx. rewrite /core /= Hx /=.
      case (total y)=> [cy ->]; eauto.
    - intros x cx Hcx. move: (core_l x). by rewrite /core /= Hcx.
    - intros x cx Hcx. move: (core_idemp x). rewrite /core /= Hcx /=.
      case (total cx)=>[ccx ->]; by constructor.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End ra_total.

(** ** CMRA for the unit type *)
Section unit.
  Instance unit_valid : Valid () := λ x, True.
  Instance unit_validN : ValidN () := λ n x, True.
  Instance unit_pcore : PCore () := λ x, Some x.
  Instance unit_op : Op () := λ x y, ().
  Lemma unit_cmra_mixin : CmraMixin ().
  Proof. apply discrete_cmra_mixin, ra_total_mixin; by eauto. Qed.
  Canonical Structure unitR : cmraT := CmraT unit unit_cmra_mixin.

  Instance unit_unit : Unit () := ().
  Lemma unit_ucmra_mixin : UcmraMixin ().
  Proof. done. Qed.
  Canonical Structure unitUR : ucmraT := UcmraT unit unit_ucmra_mixin.

  Global Instance unit_cmra_discrete : CmraDiscrete unitR.
  Proof. done. Qed.
  Global Instance unit_core_id (x : ()) : CoreId x.
  Proof. by constructor. Qed.
  Global Instance unit_cancelable (x : ()) : Cancelable x.
  Proof. by constructor. Qed.
End unit.

(** ** Natural numbers *)
Section nat.
  Instance nat_valid : Valid nat := λ x, True.
  Instance nat_validN : ValidN nat := λ n x, True.
  Instance nat_pcore : PCore nat := λ x, Some 0.
  Instance nat_op : Op nat := plus.
  Definition nat_op_plus x y : x ⋅ y = x + y := eq_refl.
  Lemma nat_included (x y : nat) : x ≼ y ↔ x ≤ y.
  Proof. by rewrite nat_le_sum. Qed.
  Lemma nat_ra_mixin : RAMixin nat.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - intros x y z. apply Nat.add_assoc.
    - intros x y. apply Nat.add_comm.
    - by exists 0.
  Qed.
  Canonical Structure natR : cmraT := discreteR nat nat_ra_mixin.

  Global Instance nat_cmra_discrete : CmraDiscrete natR.
  Proof. apply discrete_cmra_discrete. Qed.

  Instance nat_unit : Unit nat := 0.
  Lemma nat_ucmra_mixin : UcmraMixin nat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure natUR : ucmraT := UcmraT nat nat_ucmra_mixin.

  Global Instance nat_cancelable (x : nat) : Cancelable x.
  Proof. by intros ???? ?%Nat.add_cancel_l. Qed.
End nat.

Definition mnat := nat.

Section mnat.
  Instance mnat_unit : Unit mnat := 0.
  Instance mnat_valid : Valid mnat := λ x, True.
  Instance mnat_validN : ValidN mnat := λ n x, True.
  Instance mnat_pcore : PCore mnat := Some.
  Instance mnat_op : Op mnat := Nat.max.
  Definition mnat_op_max x y : x ⋅ y = x `max` y := eq_refl.
  Lemma mnat_included (x y : mnat) : x ≼ y ↔ x ≤ y.
  Proof.
    split.
    - intros [z ->]; unfold op, mnat_op; lia.
    - exists y. by symmetry; apply Nat.max_r.
  Qed.
  Lemma mnat_ra_mixin : RAMixin mnat.
  Proof.
    apply ra_total_mixin; try by eauto.
    - solve_proper.
    - solve_proper.
    - intros x y z. apply Nat.max_assoc.
    - intros x y. apply Nat.max_comm.
    - intros x. apply Max.max_idempotent.
  Qed.
  Canonical Structure mnatR : cmraT := discreteR mnat mnat_ra_mixin.

  Global Instance mnat_cmra_discrete : CmraDiscrete mnatR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma mnat_ucmra_mixin : UcmraMixin mnat.
  Proof. split; apply _ || done. Qed.
  Canonical Structure mnatUR : ucmraT := UcmraT mnat mnat_ucmra_mixin.

  Global Instance mnat_core_id (x : mnat) : CoreId x.
  Proof. by constructor. Qed.
End mnat.

(** ** Positive integers. *)
Section positive.
  Instance pos_valid : Valid positive := λ x, True.
  Instance pos_validN : ValidN positive := λ n x, True.
  Instance pos_pcore : PCore positive := λ x, None.
  Instance pos_op : Op positive := Pos.add.
  Definition pos_op_plus x y : x ⋅ y = (x + y)%positive := eq_refl.
  Lemma pos_included (x y : positive) : x ≼ y ↔ (x < y)%positive.
  Proof. by rewrite Plt_sum. Qed.
  Lemma pos_ra_mixin : RAMixin positive.
  Proof.
    split; try by eauto.
    - by intros ??? ->.
    - intros ???. apply Pos.add_assoc.
    - intros ??. apply Pos.add_comm.
  Qed.
  Canonical Structure positiveR : cmraT := discreteR positive pos_ra_mixin.

  Global Instance pos_cmra_discrete : CmraDiscrete positiveR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance pos_cancelable (x : positive) : Cancelable x.
  Proof. intros n y z ??. by eapply Pos.add_reg_l, leibniz_equiv. Qed.
  Global Instance pos_id_free (x : positive) : IdFree x.
  Proof.
    intros y ??. apply (Pos.add_no_neutral x y). rewrite Pos.add_comm.
    by apply leibniz_equiv.
  Qed.
End positive.

(** ** Product *)
Section prod.
  Context {A B : cmraT}.
  Local Arguments pcore _ _ !_ /.
  Local Arguments cmra_pcore _ !_/.

  Instance prod_op : Op (A * B) := λ x y, (x.1 ⋅ y.1, x.2 ⋅ y.2).
  Instance prod_pcore : PCore (A * B) := λ x,
    c1 ← pcore (x.1); c2 ← pcore (x.2); Some (c1, c2).
  Arguments prod_pcore !_ /.
  Instance prod_valid : Valid (A * B) := λ x, ✓ x.1 ∧ ✓ x.2.
  Instance prod_validN : ValidN (A * B) := λ n x, ✓{n} x.1 ∧ ✓{n} x.2.

  Lemma prod_pcore_Some (x cx : A * B) :
    pcore x = Some cx ↔ pcore (x.1) = Some (cx.1) ∧ pcore (x.2) = Some (cx.2).
  Proof. destruct x, cx; by intuition simplify_option_eq. Qed.
  Lemma prod_pcore_Some' (x cx : A * B) :
    pcore x ≡ Some cx ↔ pcore (x.1) ≡ Some (cx.1) ∧ pcore (x.2) ≡ Some (cx.2).
  Proof.
    split; [by intros (cx'&[-> ->]%prod_pcore_Some&->)%equiv_Some_inv_r'|].
    rewrite {3}/pcore /prod_pcore. (* TODO: use setoid rewrite *)
    intros [Hx1 Hx2]; inversion_clear Hx1; simpl; inversion_clear Hx2.
    by constructor.
  Qed.

  Lemma prod_included (x y : A * B) : x ≼ y ↔ x.1 ≼ y.1 ∧ x.2 ≼ y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.
  Lemma prod_includedN (x y : A * B) n : x ≼{n} y ↔ x.1 ≼{n} y.1 ∧ x.2 ≼{n} y.2.
  Proof.
    split; [intros [z Hz]; split; [exists (z.1)|exists (z.2)]; apply Hz|].
    intros [[z1 Hz1] [z2 Hz2]]; exists (z1,z2); split; auto.
  Qed.

  Definition prod_cmra_mixin : CmraMixin (A * B).
  Proof.
    split; try apply _.
    - by intros n x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2.
    - intros n x y cx; setoid_rewrite prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_ne n (x.1) (y.1) (cx.1)) as (z1&->&?); auto.
      destruct (cmra_pcore_ne n (x.2) (y.2) (cx.2)) as (z2&->&?); auto.
      exists (z1,z2); repeat constructor; auto.
    - by intros n y1 y2 [Hy1 Hy2] [??]; split; rewrite /= -?Hy1 -?Hy2.
    - intros x; split.
      + intros [??] n; split; by apply cmra_valid_validN.
      + intros Hxy; split; apply cmra_valid_validN=> n; apply Hxy.
    - by intros n x [??]; split; apply cmra_validN_S.
    - by split; rewrite /= assoc.
    - by split; rewrite /= comm.
    - intros x y [??]%prod_pcore_Some;
        constructor; simpl; eauto using cmra_pcore_l.
    - intros x y; rewrite prod_pcore_Some prod_pcore_Some'.
      naive_solver eauto using cmra_pcore_idemp.
    - intros x y cx; rewrite prod_included prod_pcore_Some=> -[??] [??].
      destruct (cmra_pcore_mono (x.1) (y.1) (cx.1)) as (z1&?&?); auto.
      destruct (cmra_pcore_mono (x.2) (y.2) (cx.2)) as (z2&?&?); auto.
      exists (z1,z2). by rewrite prod_included prod_pcore_Some.
    - intros n x y [??]; split; simpl in *; eauto using cmra_validN_op_l.
    - intros n x y1 y2 [??] [??]; simpl in *.
      destruct (cmra_extend n (x.1) (y1.1) (y2.1)) as (z11&z12&?&?&?); auto.
      destruct (cmra_extend n (x.2) (y1.2) (y2.2)) as (z21&z22&?&?&?); auto.
      by exists (z11,z21), (z12,z22).
  Qed.
  Canonical Structure prodR := CmraT (prod A B) prod_cmra_mixin.

  Lemma pair_op (a a' : A) (b b' : B) : (a, b) ⋅ (a', b') = (a ⋅ a', b ⋅ b').
  Proof. done. Qed.

  Global Instance prod_cmra_total : CmraTotal A → CmraTotal B → CmraTotal prodR.
  Proof.
    intros H1 H2 [a b]. destruct (H1 a) as [ca ?], (H2 b) as [cb ?].
    exists (ca,cb); by simplify_option_eq.
  Qed.

  Global Instance prod_cmra_discrete :
    CmraDiscrete A → CmraDiscrete B → CmraDiscrete prodR.
  Proof. split. apply _. by intros ? []; split; apply cmra_discrete_valid. Qed.

  Global Instance pair_core_id x y :
    CoreId x → CoreId y → CoreId (x,y).
  Proof. by rewrite /CoreId prod_pcore_Some'. Qed.

  Global Instance pair_exclusive_l x y : Exclusive x → Exclusive (x,y).
  Proof. by intros ?[][?%exclusive0_l]. Qed.
  Global Instance pair_exclusive_r x y : Exclusive y → Exclusive (x,y).
  Proof. by intros ?[][??%exclusive0_l]. Qed.

  Global Instance pair_cancelable x y :
    Cancelable x → Cancelable y → Cancelable (x,y).
  Proof. intros ???[][][][]. constructor; simpl in *; by eapply cancelableN. Qed.

  Global Instance pair_id_free_l x y : IdFree x → IdFree (x,y).
  Proof. move=>? [??] [? _] [/=? _]. eauto. Qed.
  Global Instance pair_id_free_r x y : IdFree y → IdFree (x,y).
  Proof. move=>? [??] [_ ?] [_ /=?]. eauto. Qed.
End prod.

Arguments prodR : clear implicits.

Section prod_unit.
  Context {A B : ucmraT}.

  Instance prod_unit `{Unit A, Unit B} : Unit (A * B) := (ε, ε).
  Lemma prod_ucmra_mixin : UcmraMixin (A * B).
  Proof.
    split.
    - split; apply ucmra_unit_valid.
    - by split; rewrite /=left_id.
    - rewrite prod_pcore_Some'; split; apply (core_id _).
  Qed.
  Canonical Structure prodUR := UcmraT (prod A B) prod_ucmra_mixin.

  Lemma pair_split (x : A) (y : B) : (x, y) ≡ (x, ε) ⋅ (ε, y).
  Proof. by rewrite pair_op left_id right_id. Qed.

  Lemma pair_split_L `{!LeibnizEquiv A, !LeibnizEquiv B} (x : A) (y : B) :
    (x, y) = (x, ε) ⋅ (ε, y).
  Proof. unfold_leibniz. apply pair_split. Qed.
End prod_unit.

Arguments prodUR : clear implicits.

Instance prod_map_cmra_morphism {A A' B B' : cmraT} (f : A → A') (g : B → B') :
  CmraMorphism f → CmraMorphism g → CmraMorphism (prod_map f g).
Proof.
  split; first apply _.
  - by intros n x [??]; split; simpl; apply cmra_morphism_validN.
  - intros x. etrans. apply (reflexivity (mbind _ _)).
    etrans; last apply (reflexivity (_ <$> mbind _ _)). simpl.
    assert (Hf := cmra_morphism_pcore f (x.1)).
    destruct (pcore (f (x.1))), (pcore (x.1)); inversion_clear Hf=>//=.
    assert (Hg := cmra_morphism_pcore g (x.2)).
    destruct (pcore (g (x.2))), (pcore (x.2)); inversion_clear Hg=>//=.
    by setoid_subst.
  - intros. by rewrite /prod_map /= -!cmra_morphism_op.
Qed.

Program Definition prodRF (F1 F2 : rFunctor) : rFunctor := {|
  rFunctor_car A B := prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (rFunctor_map F1 fg) (rFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply rFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !rFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !rFunctor_compose.
Qed.
Notation "F1 * F2" := (prodRF F1%RF F2%RF) : rFunctor_scope.

Instance prodRF_contractive F1 F2 :
  rFunctorContractive F1 → rFunctorContractive F2 →
  rFunctorContractive (prodRF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply rFunctor_contractive.
Qed.

Program Definition prodURF (F1 F2 : urFunctor) : urFunctor := {|
  urFunctor_car A B := prodUR (urFunctor_car F1 A B) (urFunctor_car F2 A B);
  urFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (urFunctor_map F1 fg) (urFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n ???. by apply prodC_map_ne; apply urFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !urFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !urFunctor_compose.
Qed.
Notation "F1 * F2" := (prodURF F1%URF F2%URF) : urFunctor_scope.

Instance prodURF_contractive F1 F2 :
  urFunctorContractive F1 → urFunctorContractive F2 →
  urFunctorContractive (prodURF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply urFunctor_contractive.
Qed.

(** ** CMRA for the option type *)
Section option.
  Context {A : cmraT}.
  Implicit Types a b : A.
  Implicit Types ma mb : option A.
  Local Arguments core _ _ !_ /.
  Local Arguments pcore _ _ !_ /.

  Instance option_valid : Valid (option A) := λ ma,
    match ma with Some a => ✓ a | None => True end.
  Instance option_validN : ValidN (option A) := λ n ma,
    match ma with Some a => ✓{n} a | None => True end.
  Instance option_pcore : PCore (option A) := λ ma, Some (ma ≫= pcore).
  Arguments option_pcore !_ /.
  Instance option_op : Op (option A) := union_with (λ a b, Some (a ⋅ b)).

  Definition Some_valid a : ✓ Some a ↔ ✓ a := reflexivity _.
  Definition Some_validN a n : ✓{n} Some a ↔ ✓{n} a := reflexivity _.
  Definition Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b := eq_refl.
  Lemma Some_core `{CmraTotal A} a : Some (core a) = core (Some a).
  Proof. rewrite /core /=. by destruct (cmra_total a) as [? ->]. Qed.
  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof. by destruct ma. Qed.

  Lemma option_included ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto;
        setoid_subst; eauto using cmra_included_l.
    - intros [->|(a&b&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.

  Lemma option_includedN n ma mb :
    ma ≼{n} mb ↔ ma = None ∨ ∃ x y, ma = Some x ∧ mb = Some y ∧ (x ≡{n}≡ y ∨ x ≼{n} y).
  Proof.
    split.
    - intros [mc Hmc].
      destruct ma as [a|]; [right|by left].
      destruct mb as [b|]; [exists a, b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto;
        ofe_subst; eauto using cmra_includedN_l.
    - intros [->|(a&y&->&->&[Hc|[c Hc]])].
      + exists mb. by destruct mb.
      + exists None; by constructor.
      + exists (Some c); by constructor.
  Qed.

  Lemma option_cmra_mixin : CmraMixin (option A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros [a|] n; destruct 1; constructor; ofe_subst.
    - destruct 1; by ofe_subst.
    - by destruct 1; rewrite /validN /option_validN //=; ofe_subst.
    - intros [a|]; [apply cmra_valid_validN|done].
    - intros n [a|]; unfold validN, option_validN; eauto using cmra_validN_S.
    - intros [a|] [b|] [c|]; constructor; rewrite ?assoc; auto.
    - intros [a|] [b|]; constructor; rewrite 1?comm; auto.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; constructor; eauto using cmra_pcore_l.
    - intros [a|]; simpl; auto.
      destruct (pcore a) as [ca|] eqn:?; simpl; eauto using cmra_pcore_idemp.
    - intros ma mb; setoid_rewrite option_included.
      intros [->|(a&b&->&->&[?|?])]; simpl; eauto.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_proper a b ca) as (?&?&?); eauto 10.
      + destruct (pcore a) as [ca|] eqn:?; eauto.
        destruct (cmra_pcore_mono a b ca) as (?&?&?); eauto 10.
    - intros n [a|] [b|]; rewrite /validN /option_validN /=;
        eauto using cmra_validN_op_l.
    - intros n ma mb1 mb2.
      destruct ma as [a|], mb1 as [b1|], mb2 as [b2|]; intros Hx Hx';
        (try by exfalso; inversion Hx'); (try (apply (inj Some) in Hx')).
      + destruct (cmra_extend n a b1 b2) as (c1&c2&?&?&?); auto.
        by exists (Some c1), (Some c2); repeat constructor.
      + by exists (Some a), None; repeat constructor.
      + by exists None, (Some a); repeat constructor.
      + exists None, None; repeat constructor.
  Qed.
  Canonical Structure optionR := CmraT (option A) option_cmra_mixin.

  Global Instance option_cmra_discrete : CmraDiscrete A → CmraDiscrete optionR.
  Proof. split; [apply _|]. by intros [a|]; [apply (cmra_discrete_valid a)|]. Qed.

  Instance option_unit : Unit (option A) := None.
  Lemma option_ucmra_mixin : UcmraMixin optionR.
  Proof. split. done. by intros []. done. Qed.
  Canonical Structure optionUR := UcmraT (option A) option_ucmra_mixin.

  (** Misc *)
  Lemma op_None ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None.
  Proof. destruct ma, mb; naive_solver. Qed.
  Lemma op_is_Some ma mb : is_Some (ma ⋅ mb) ↔ is_Some ma ∨ is_Some mb.
  Proof. rewrite -!not_eq_None_Some op_None. destruct ma, mb; naive_solver. Qed.

  Lemma cmra_opM_assoc' a mb mc : a ⋅? mb ⋅? mc ≡ a ⋅? (mb ⋅ mc).
  Proof. destruct mb, mc; by rewrite /= -?assoc. Qed.

  Global Instance Some_core_id a : CoreId a → CoreId (Some a).
  Proof. by constructor. Qed.
  Global Instance option_core_id ma : (∀ x : A, CoreId x) → CoreId ma.
  Proof. intros. destruct ma; apply _. Qed.

  Lemma exclusiveN_Some_l n a `{!Exclusive a} mb :
    ✓{n} (Some a ⋅ mb) → mb = None.
  Proof. destruct mb. move=> /(exclusiveN_l _ a) []. done. Qed.
  Lemma exclusiveN_Some_r n a `{!Exclusive a} mb :
    ✓{n} (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusiveN_Some_l. Qed.

  Lemma exclusive_Some_l a `{!Exclusive a} mb : ✓ (Some a ⋅ mb) → mb = None.
  Proof. destruct mb. move=> /(exclusive_l a) []. done. Qed.
  Lemma exclusive_Some_r a `{!Exclusive a} mb : ✓ (mb ⋅ Some a) → mb = None.
  Proof. rewrite comm. by apply exclusive_Some_l. Qed.

  Lemma Some_includedN n a b : Some a ≼{n} Some b ↔ a ≡{n}≡ b ∨ a ≼{n} b.
  Proof. rewrite option_includedN; naive_solver. Qed.
  Lemma Some_included a b : Some a ≼ Some b ↔ a ≡ b ∨ a ≼ b.
  Proof. rewrite option_included; naive_solver. Qed.
  Lemma Some_included_2 a b : a ≼ b → Some a ≼ Some b.
  Proof. rewrite Some_included; eauto. Qed.

  Lemma Some_includedN_total `{CmraTotal A} n a b : Some a ≼{n} Some b ↔ a ≼{n} b.
  Proof. rewrite Some_includedN. split. by intros [->|?]. eauto. Qed.
  Lemma Some_included_total `{CmraTotal A} a b : Some a ≼ Some b ↔ a ≼ b.
  Proof. rewrite Some_included. split. by intros [->|?]. eauto. Qed.

  Lemma Some_includedN_exclusive n a `{!Exclusive a} b :
    Some a ≼{n} Some b → ✓{n} b → a ≡{n}≡ b.
  Proof. move=> /Some_includedN [//|/exclusive_includedN]; tauto. Qed.
  Lemma Some_included_exclusive a `{!Exclusive a} b :
    Some a ≼ Some b → ✓ b → a ≡ b.
  Proof. move=> /Some_included [//|/exclusive_included]; tauto. Qed.

  Lemma is_Some_includedN n ma mb : ma ≼{n} mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_includedN. naive_solver. Qed.
  Lemma is_Some_included ma mb : ma ≼ mb → is_Some ma → is_Some mb.
  Proof. rewrite -!not_eq_None_Some option_included. naive_solver. Qed.

  Global Instance cancelable_Some a :
    IdFree a → Cancelable a → Cancelable (Some a).
  Proof.
    intros Hirr ?? [b|] [c|] ? EQ; inversion_clear EQ.
    - constructor. by apply (cancelableN a).
    - destruct (Hirr b); [|eauto using dist_le with lia].
      by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia.
    - destruct (Hirr c); [|symmetry; eauto using dist_le with lia].
      by eapply (cmra_validN_le n); last lia.
    - done.
  Qed.
End option.

Arguments optionR : clear implicits.
Arguments optionUR : clear implicits.

Section option_prod.
  Context {A B : cmraT}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma Some_pair_includedN n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ Some b1 ≼{n} Some b2.
  Proof. rewrite !Some_includedN. intros [[??]|[??]%prod_includedN]; eauto. Qed.
  Lemma Some_pair_includedN_total_1 `{CmraTotal A} n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → a1 ≼{n} a2 ∧ Some b1 ≼{n} Some b2.
  Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ a1). Qed.
  Lemma Some_pair_includedN_total_2 `{CmraTotal B} n a1 a2 b1 b2 :
    Some (a1,b1) ≼{n} Some (a2,b2) → Some a1 ≼{n} Some a2 ∧ b1 ≼{n} b2.
  Proof. intros ?%Some_pair_includedN. by rewrite -(Some_includedN_total _ b1). Qed.

  Lemma Some_pair_included a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ Some b1 ≼ Some b2.
  Proof. rewrite !Some_included. intros [[??]|[??]%prod_included]; eauto. Qed.
  Lemma Some_pair_included_total_1 `{CmraTotal A} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → a1 ≼ a2 ∧ Some b1 ≼ Some b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total a1). Qed.
  Lemma Some_pair_included_total_2 `{CmraTotal B} a1 a2 b1 b2 :
    Some (a1,b1) ≼ Some (a2,b2) → Some a1 ≼ Some a2 ∧ b1 ≼ b2.
  Proof. intros ?%Some_pair_included. by rewrite -(Some_included_total b1). Qed.
End option_prod.

Instance option_fmap_cmra_morphism {A B : cmraT} (f: A → B) `{!CmraMorphism f} :
  CmraMorphism (fmap f : option A → option B).
Proof.
  split; first apply _.
  - intros n [a|] ?; rewrite /cmra_validN //=. by apply (cmra_morphism_validN f).
  - move=> [a|] //. by apply Some_proper, cmra_morphism_pcore.
  - move=> [a|] [b|] //=. by rewrite -(cmra_morphism_op f).
Qed.

Program Definition optionRF (F : rFunctor) : rFunctor := {|
  rFunctor_car A B := optionR (rFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply rFunctor_compose.
Qed.

Instance optionRF_contractive F :
  rFunctorContractive F → rFunctorContractive (optionRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive.
Qed.

Program Definition optionURF (F : rFunctor) : urFunctor := {|
  urFunctor_car A B := optionUR (rFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := optionC_map (rFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply rFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply rFunctor_compose.
Qed.

Instance optionURF_contractive F :
  rFunctorContractive F → urFunctorContractive (optionURF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, rFunctor_contractive.
Qed.

(* Dependently-typed functions over a finite discrete domain *)
Section ofe_fun_cmra.
  Context `{B : A → ucmraT}.
  Implicit Types f g : ofe_fun B.

  Instance ofe_fun_op : Op (ofe_fun B) := λ f g x, f x ⋅ g x.
  Instance ofe_fun_pcore : PCore (ofe_fun B) := λ f, Some (λ x, core (f x)).
  Instance ofe_fun_valid : Valid (ofe_fun B) := λ f, ∀ x, ✓ f x.
  Instance ofe_fun_validN : ValidN (ofe_fun B) := λ n f, ∀ x, ✓{n} f x.

  Definition ofe_fun_lookup_op f g x : (f ⋅ g) x = f x ⋅ g x := eq_refl.
  Definition ofe_fun_lookup_core f x : (core f) x = core (f x) := eq_refl.

  Lemma ofe_fun_included_spec_1 (f g : ofe_fun B) x : f ≼ g → f x ≼ g x.
  Proof. by intros [h Hh]; exists (h x); rewrite /op /ofe_fun_op (Hh x). Qed.

  Lemma ofe_fun_included_spec `{Hfin : Finite A} (f g : ofe_fun B) : f ≼ g ↔ ∀ x, f x ≼ g x.
  Proof.
    split; [by intros; apply ofe_fun_included_spec_1|].
    intros [h ?]%finite_choice; by exists h.
  Qed.

  Lemma ofe_fun_cmra_mixin : CmraMixin (ofe_fun B).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - by intros n f1 f2 f3 Hf x; rewrite ofe_fun_lookup_op (Hf x).
    - by intros n f1 f2 Hf x; rewrite ofe_fun_lookup_core (Hf x).
    - by intros n f1 f2 Hf ? x; rewrite -(Hf x).
    - intros g; split.
      + intros Hg n i; apply cmra_valid_validN, Hg.
      + intros Hg i; apply cmra_valid_validN=> n; apply Hg.
    - intros n f Hf x; apply cmra_validN_S, Hf.
    - by intros f1 f2 f3 x; rewrite ofe_fun_lookup_op assoc.
    - by intros f1 f2 x; rewrite ofe_fun_lookup_op comm.
    - by intros f x; rewrite ofe_fun_lookup_op ofe_fun_lookup_core cmra_core_l.
    - by intros f x; rewrite ofe_fun_lookup_core cmra_core_idemp.
    - intros f1 f2 Hf12. exists (core f2)=>x. rewrite ofe_fun_lookup_op.
      apply (ofe_fun_included_spec_1 _ _ x), (cmra_core_mono (f1 x)) in Hf12.
      rewrite !ofe_fun_lookup_core. destruct Hf12 as [? ->].
      rewrite assoc -cmra_core_dup //.
    - intros n f1 f2 Hf x; apply cmra_validN_op_l with (f2 x), Hf.
    - intros n f f1 f2 Hf Hf12.
      assert (FUN := λ x, cmra_extend n (f x) (f1 x) (f2 x) (Hf x) (Hf12 x)).
      exists (λ x, projT1 (FUN x)), (λ x, proj1_sig (projT2 (FUN x))).
      split; [|split]=>x; [rewrite ofe_fun_lookup_op| |];
      by destruct (FUN x) as (?&?&?&?&?).
  Qed.
  Canonical Structure ofe_funR := CmraT (ofe_fun B) ofe_fun_cmra_mixin.

  Instance ofe_fun_unit : Unit (ofe_fun B) := λ x, ε.
  Definition ofe_fun_lookup_empty x : ε x = ε := eq_refl.

  Lemma ofe_fun_ucmra_mixin : UcmraMixin (ofe_fun B).
  Proof.
    split.
    - intros x; apply ucmra_unit_valid.
    - by intros f x; rewrite ofe_fun_lookup_op left_id.
    - constructor=> x. apply core_id_core, _.
  Qed.
  Canonical Structure ofe_funUR := UcmraT (ofe_fun B) ofe_fun_ucmra_mixin.

  Global Instance ofe_fun_unit_discrete :
    (∀ i, Discrete (ε : B i)) → Discrete (ε : ofe_fun B).
  Proof. intros ? f Hf x. by apply: discrete. Qed.
End ofe_fun_cmra.

Arguments ofe_funR {_} _.
Arguments ofe_funUR {_} _.

Instance ofe_fun_map_cmra_morphism {A} {B1 B2 : A → ucmraT} (f : ∀ x, B1 x → B2 x) :
  (∀ x, CmraMorphism (f x)) → CmraMorphism (ofe_fun_map f).
Proof.
  split; first apply _.
  - intros n g Hg x; rewrite /ofe_fun_map; apply (cmra_morphism_validN (f _)), Hg.
  - intros. apply Some_proper=>i. apply (cmra_morphism_core (f i)).
  - intros g1 g2 i. by rewrite /ofe_fun_map ofe_fun_lookup_op cmra_morphism_op.
Qed.

Program Definition ofe_funURF {C} (F : C → urFunctor) : urFunctor := {|
  urFunctor_car A B := ofe_funUR (λ c, urFunctor_car (F c) A B);
  urFunctor_map A1 A2 B1 B2 fg := ofe_funC_map (λ c, urFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C F A1 A2 B1 B2 n ?? g. by apply ofe_funC_map_ne=>?; apply urFunctor_ne.
Qed.
Next Obligation.
  intros C F A B g; simpl. rewrite -{2}(ofe_fun_map_id g).
  apply ofe_fun_map_ext=> y; apply urFunctor_id.
Qed.
Next Obligation.
  intros C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /=-ofe_fun_map_compose.
  apply ofe_fun_map_ext=>y; apply urFunctor_compose.
Qed.
Instance ofe_funURF_contractive {C} (F : C → urFunctor) :
  (∀ c, urFunctorContractive (F c)) → urFunctorContractive (ofe_funURF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply ofe_funC_map_ne=>c; apply urFunctor_contractive.
Qed.
