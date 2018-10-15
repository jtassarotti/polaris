From iris.base_logic Require Export base_logic.
Set Default Proof Using "Type".
Import uPred.

(* The Or class is useful for efficiency: instead of having two instances
[P → Q1 → R] and [P → Q2 → R] we could have one instance [P → Or Q1 Q2 → R],
which avoids the need to derive [P] twice. *)
Inductive Or (P1 P2 : Type) :=
  | Or_l : P1 → Or P1 P2
  | Or_r : P2 → Or P1 P2.
Existing Class Or.
Existing Instance Or_l | 9.
Existing Instance Or_r | 10.

Class FromAssumption {M} (p : bool) (P Q : uPred M) :=
  from_assumption : □?p P ⊢ Q.
Arguments from_assumption {_} _ _ _ {_}.
(* No need to restrict Hint Mode, we have a default instance that will persistently
be used in case of evars *)
Hint Mode FromAssumption + + - - : typeclass_instances.

Class IntoPure {M} (P : uPred M) (φ : Prop) := into_pure : P ⊢ ⌜φ⌝.
Arguments into_pure {_} _ _ {_}.
Hint Mode IntoPure + ! - : typeclass_instances.

(* [IntoPureT] is a variant of [IntoPure] with the argument in [Type] to avoid
some shortcoming of unification in Coq's type class search. An example where we
use this workaround is to repair the following instance:

  Global Instance into_exist_and_pure P Q (φ : Prop) :
    IntoPure P φ → IntoExist (P ∧ Q) (λ _ : φ, Q).

Coq is unable to use this instance: [class_apply] -- which is used by type class
search -- fails with the error that it cannot unify [Prop] and [Type]. This is
probably caused because [class_apply] uses an ancient unification algorith. The
[refine] tactic -- which uses a better unification algorithm -- succeeds to
apply the above instance.

Since we do not want to define [Hint Extern] declarations using [refine] for
any instance like [into_exist_and_pure], we factor this out in the class
[IntoPureT]. This way, we only have to declare a [Hint Extern] using [refine]
once, and use [IntoPureT] in any instance like [into_exist_and_pure].

TODO: Report this as a Coq bug, or wait for https://github.com/coq/coq/pull/991
to be finished and merged someday. *)
Class IntoPureT {M} (P : uPred M) (φ : Type) :=
  into_pureT : ∃ ψ : Prop, φ = ψ ∧ IntoPure P ψ.
Lemma into_pureT_hint {M} (P : uPred M) (φ : Prop) : IntoPure P φ → IntoPureT P φ.
Proof. by exists φ. Qed.
Hint Extern 0 (IntoPureT _ _) =>
  notypeclasses refine (into_pureT_hint _ _ _) : typeclass_instances.

Class FromPure {M} (P : uPred M) (φ : Prop) := from_pure : ⌜φ⌝ ⊢ P.
Arguments from_pure {_} _ _ {_}.
Hint Mode FromPure + ! - : typeclass_instances.

Class IntoInternalEq {M} {A : ofeT} (P : uPred M) (x y : A) :=
  into_internal_eq : P ⊢ x ≡ y.
Arguments into_internal_eq {_ _} _ _ _ {_}.
Hint Mode IntoInternalEq + - ! - - : typeclass_instances.

Class IntoPersistent {M} (p : bool) (P Q : uPred M) :=
  into_persistent : □?p P ⊢ □ Q.
Arguments into_persistent {_} _ _ _ {_}.
Hint Mode IntoPersistent + + ! - : typeclass_instances.

Class FromAlways {M} (p : bool) (P Q : uPred M) :=
  from_always : (if p then ■ Q else □ Q) ⊢ P.
Arguments from_always {_} _ _ _ {_}.
Hint Mode FromAlways + - ! - : typeclass_instances.

(* The class [IntoLaterN] has only two instances:

- The default instance [IntoLaterN n P P], i.e. [▷^n P -∗ P]
- The instance [IntoLaterN' n P Q → IntoLaterN n P Q], where [IntoLaterN']
  is identical to [IntoLaterN], but computationally is supposed to make
  progress, i.e. its instances should actually strip a later.

The point of using the auxilary class [IntoLaterN'] is to ensure that the
default instance is not applied deeply in the term, which may cause in too many
definitions being unfolded (see issue #55).

For binary connectives we have the following instances:

<<
IntoLaterN' n P P'       IntoLaterN n Q Q'
------------------------------------------
     IntoLaterN' n (P /\ Q) (P' /\ Q')


      IntoLaterN' n Q Q'
-------------------------------
IntoLaterN n (P /\ Q) (P /\ Q')
>>
*)
Class IntoLaterN {M} (n : nat) (P Q : uPred M) := into_laterN : P ⊢ ▷^n Q.
Arguments into_laterN {_} _ _ _ {_}.
Hint Mode IntoLaterN + - - - : typeclass_instances.

Class IntoLaterN' {M} (n : nat) (P Q : uPred M) :=
  into_laterN' :> IntoLaterN n P Q.
Arguments into_laterN' {_} _ _ _ {_}.
Hint Mode IntoLaterN' + - ! - : typeclass_instances.

Instance into_laterN_default {M} n (P : uPred M) : IntoLaterN n P P | 1000.
Proof. apply laterN_intro. Qed.

Class FromLaterN {M} (n : nat) (P Q : uPred M) := from_laterN : ▷^n Q ⊢ P.
Arguments from_laterN {_} _ _ _ {_}.
Hint Mode FromLaterN + - ! - : typeclass_instances.

Class WandWeaken {M} (p : bool) (P Q P' Q' : uPred M) :=
  wand_weaken : (P -∗ Q) ⊢ (□?p P' -∗ Q').
Hint Mode WandWeaken + + - - - - : typeclass_instances.

Class WandWeaken' {M} (p : bool) (P Q P' Q' : uPred M) :=
  wand_weaken' :> WandWeaken p P Q P' Q'.
Hint Mode WandWeaken' + + - - ! - : typeclass_instances.
Hint Mode WandWeaken' + + - - - ! : typeclass_instances.

Class IntoWand {M} (p : bool) (R P Q : uPred M) := into_wand : R ⊢ □?p P -∗ Q.
Arguments into_wand {_} _ _ _ _ {_}.
Hint Mode IntoWand + + ! - - : typeclass_instances.

Class FromAnd {M} (p : bool) (P Q1 Q2 : uPred M) :=
  from_and : (if p then Q1 ∧ Q2 else Q1 ∗ Q2) ⊢ P.
Arguments from_and {_} _ _ _ _ {_}.
Hint Mode FromAnd + + ! - - : typeclass_instances.
Hint Mode FromAnd + + - ! ! : typeclass_instances. (* For iCombine *)

Lemma mk_from_and_and {M} p (P Q1 Q2 : uPred M) :
  (Q1 ∧ Q2 ⊢ P) → FromAnd p P Q1 Q2.
Proof. rewrite /FromAnd=><-. destruct p; auto using sep_and. Qed.
Lemma mk_from_and_persistent {M} (P Q1 Q2 : uPred M) :
  Or (Persistent Q1) (Persistent Q2) → (Q1 ∗ Q2 ⊢ P) → FromAnd true P Q1 Q2.
Proof.
  intros [?|?] ?; rewrite /FromAnd.
  - by rewrite and_sep_l.
  - by rewrite and_sep_r.
Qed.

Class IntoAnd {M} (p : bool) (P Q1 Q2 : uPred M) :=
  into_and : P ⊢ if p then Q1 ∧ Q2 else Q1 ∗ Q2.
Arguments into_and {_} _ _ _ _ {_}.
Hint Mode IntoAnd + + ! - - : typeclass_instances.

Lemma mk_into_and_sep {M} p (P Q1 Q2 : uPred M) :
  (P ⊢ Q1 ∗ Q2) → IntoAnd p P Q1 Q2.
Proof. rewrite /IntoAnd=>->. destruct p; auto using sep_and. Qed.

(* There are various versions of [IsOp] with different modes:

- [IsOp a b1 b2]: this one has no mode, it can be used regardless of whether
  any of the arguments is an evar. This class has only one direct instance:
  [IsOp (a ⋅ b) a b].
- [IsOp' a b1 b2]: requires either [a] to start with a constructor, OR [b1] and
  [b2] to start with a constructor. All usual instances should be of this
  class to avoid loops.
- [IsOp'LR a b1 b2]: requires either [a] to start with a constructor. This one
  has just one instance: [IsOp'LR (a ⋅ b) a b] with a very low precendence.
  This is important so that when performing, for example, an [iDestruct] on
  [own γ (q1 + q2)] where [q1] and [q2] are fractions, we actually get
  [own γ q1] and [own γ q2] instead of [own γ ((q1 + q2)/2)] twice.
*)
Class IsOp {A : cmraT} (a b1 b2 : A) := is_op : a ≡ b1 ⋅ b2.
Arguments is_op {_} _ _ _ {_}.
Hint Mode IsOp + - - - : typeclass_instances.

Instance is_op_op {A : cmraT} (a b : A) : IsOp (a ⋅ b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : cmraT} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Hint Mode IsOp' + ! - - : typeclass_instances.
Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : cmraT} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Hint Mode IsOp'LR + ! - - : typeclass_instances.
Instance is_op_lr_op {A : cmraT} (a b : A) : IsOp'LR (a ⋅ b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

Class Frame {M} (p : bool) (R P Q : uPred M) := frame : □?p R ∗ Q ⊢ P.
Arguments frame {_ _} _ _ _ {_}.
Hint Mode Frame + + ! ! - : typeclass_instances.

Class MaybeFrame {M} (p : bool) (R P Q : uPred M) := maybe_frame : □?p R ∗ Q ⊢ P.
Arguments maybe_frame {_} _ _ _ {_}.
Hint Mode MaybeFrame + + ! ! - : typeclass_instances.

Instance maybe_frame_frame {M} p (R P Q : uPred M) :
  Frame p R P Q → MaybeFrame p R P Q.
Proof. done. Qed.
Instance maybe_frame_default {M} p (R P : uPred M) : MaybeFrame p R P P | 100.
Proof. apply sep_elim_r. Qed.

Class FromOr {M} (P Q1 Q2 : uPred M) := from_or : Q1 ∨ Q2 ⊢ P.
Arguments from_or {_} _ _ _ {_}.
Hint Mode FromOr + ! - - : typeclass_instances.

Class IntoOr {M} (P Q1 Q2 : uPred M) := into_or : P ⊢ Q1 ∨ Q2.
Arguments into_or {_} _ _ _ {_}.
Hint Mode IntoOr + ! - - : typeclass_instances.

Class FromExist {M A} (P : uPred M) (Φ : A → uPred M) :=
  from_exist : (∃ x, Φ x) ⊢ P.
Arguments from_exist {_ _} _ _ {_}.
Hint Mode FromExist + - ! - : typeclass_instances.

Class IntoExist {M A} (P : uPred M) (Φ : A → uPred M) :=
  into_exist : P ⊢ ∃ x, Φ x.
Arguments into_exist {_ _} _ _ {_}.
Hint Mode IntoExist + - ! - : typeclass_instances.

Class IntoForall {M A} (P : uPred M) (Φ : A → uPred M) :=
  into_forall : P ⊢ ∀ x, Φ x.
Arguments into_forall {_ _} _ _ {_}.
Hint Mode IntoForall + - ! - : typeclass_instances.

Class FromForall {M A} (P : uPred M) (Φ : A → uPred M) :=
  from_forall : (∀ x, Φ x) ⊢ P.
Arguments from_forall {_ _} _ _ {_}.
Hint Mode FromForall + - ! - : typeclass_instances.

Class FromModal {M} (P Q : uPred M) := from_modal : Q ⊢ P.
Arguments from_modal {_} _ _ {_}.
Hint Mode FromModal + ! - : typeclass_instances.

Class ElimModal {M} (P P' : uPred M) (Q Q' : uPred M) :=
  elim_modal : P ∗ (P' -∗ Q') ⊢ Q.
Arguments elim_modal {_} _ _ _ _ {_}.
Hint Mode ElimModal + ! - ! - : typeclass_instances.
Hint Mode ElimModal + - ! - ! : typeclass_instances.

Lemma elim_modal_dummy {M} (P Q : uPred M) : ElimModal P P Q Q.
Proof. by rewrite /ElimModal wand_elim_r. Qed.

Class IsExcept0 {M} (Q : uPred M) := is_except_0 : ◇ Q ⊢ Q.
Arguments is_except_0 {_} _ {_}.
Hint Mode IsExcept0 + ! : typeclass_instances.

Class IsCons {A} (l : list A) (x : A) (k : list A) := is_cons : l = x :: k.
Class IsApp {A} (l k1 k2 : list A) := is_app : l = k1 ++ k2.
Global Hint Mode IsCons + ! - - : typeclass_instances.
Global Hint Mode IsApp + ! - - : typeclass_instances.

Instance is_cons_cons {A} (x : A) (l : list A) : IsCons (x :: l) x l.
Proof. done. Qed.
Instance is_app_app {A} (l1 l2 : list A) : IsApp (l1 ++ l2) l1 l2.
Proof. done. Qed.

(* We make sure that tactics that perform actions on *specific* hypotheses or
parts of the goal look through the [tc_opaque] connective, which is used to make
definitions opaque for type class search. For example, when using `iDestruct`,
an explicit hypothesis is affected, and as such, we should look through opaque
definitions. However, when using `iFrame` or `iNext`, arbitrary hypotheses or
parts of the goal are affected, and as such, type class opacity should be
respected.

This means that there are [tc_opaque] instances for all proofmode type classes
with the exception of:

- [FromAssumption] used by [iAssumption]
- [Frame] used by [iFrame]
- [IntoLaterN] and [FromLaterN] used by [iNext]
- [IntoPersistent] used by [iPersistent]
*)
Instance into_pure_tc_opaque {M} (P : uPred M) φ :
  IntoPure P φ → IntoPure (tc_opaque P) φ := id.
Instance from_pure_tc_opaque {M} (P : uPred M) φ :
  FromPure P φ → FromPure (tc_opaque P) φ := id.
Instance from_laterN_tc_opaque {M} n (P Q : uPred M) :
  FromLaterN n P Q → FromLaterN n (tc_opaque P) Q := id.
Instance into_wand_tc_opaque {M} p (R P Q : uPred M) :
  IntoWand p R P Q → IntoWand p (tc_opaque R) P Q := id.
(* Higher precedence than [from_and_sep] so that [iCombine] does not loop. *)
Instance from_and_tc_opaque {M} p (P Q1 Q2 : uPred M) :
  FromAnd p P Q1 Q2 → FromAnd p (tc_opaque P) Q1 Q2 | 102 := id.
Instance into_and_tc_opaque {M} p (P Q1 Q2 : uPred M) :
  IntoAnd p P Q1 Q2 → IntoAnd p (tc_opaque P) Q1 Q2 := id.
Instance from_or_tc_opaque {M} (P Q1 Q2 : uPred M) :
  FromOr P Q1 Q2 → FromOr (tc_opaque P) Q1 Q2 := id.
Instance into_or_tc_opaque {M} (P Q1 Q2 : uPred M) :
  IntoOr P Q1 Q2 → IntoOr (tc_opaque P) Q1 Q2 := id.
Instance from_exist_tc_opaque {M A} (P : uPred M) (Φ : A → uPred M) :
  FromExist P Φ → FromExist (tc_opaque P) Φ := id.
Instance into_exist_tc_opaque {M A} (P : uPred M) (Φ : A → uPred M) :
  IntoExist P Φ → IntoExist (tc_opaque P) Φ := id.
Instance into_forall_tc_opaque {M A} (P : uPred M) (Φ : A → uPred M) :
  IntoForall P Φ → IntoForall (tc_opaque P) Φ := id.
Instance from_modal_tc_opaque {M} (P Q : uPred M) :
  FromModal P Q → FromModal (tc_opaque P) Q := id.
Instance elim_modal_tc_opaque {M} (P P' Q Q' : uPred M) :
  ElimModal P P' Q Q' → ElimModal (tc_opaque P) P' Q Q' := id.
