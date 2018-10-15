From iris.algebra Require Export cmra updates.
Set Default Proof Using "Type".

Record DraMixin A `{Equiv A, Core A, Disjoint A, Op A, Valid A} := {
  (* setoids *)
  mixin_dra_equivalence : Equivalence ((≡) : relation A);
  mixin_dra_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (⋅);
  mixin_dra_core_proper : Proper ((≡) ==> (≡)) core;
  mixin_dra_valid_proper : Proper ((≡) ==> impl) valid;
  mixin_dra_disjoint_proper x : Proper ((≡) ==> impl) (disjoint x);
  (* validity *)
  mixin_dra_op_valid x y : ✓ x → ✓ y → x ## y → ✓ (x ⋅ y);
  mixin_dra_core_valid x : ✓ x → ✓ core x;
  (* monoid *)
  mixin_dra_assoc x y z :
    ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ⋅ (y ⋅ z) ≡ (x ⋅ y) ⋅ z;
  mixin_dra_disjoint_ll x y z : ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## z;
  mixin_dra_disjoint_move_l x y z :
    ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## y ⋅ z;
  mixin_dra_symmetric : Symmetric (@disjoint A _);
  mixin_dra_comm x y : ✓ x → ✓ y → x ## y → x ⋅ y ≡ y ⋅ x;
  mixin_dra_core_disjoint_l x : ✓ x → core x ## x;
  mixin_dra_core_l x : ✓ x → core x ⋅ x ≡ x;
  mixin_dra_core_idemp x : ✓ x → core (core x) ≡ core x;
  mixin_dra_core_mono x y : 
    ∃ z, ✓ x → ✓ y → x ## y → core (x ⋅ y) ≡ core x ⋅ z ∧ ✓ z ∧ core x ## z
}.
Structure draT := DraT {
  dra_car :> Type;
  dra_equiv : Equiv dra_car;
  dra_core : Core dra_car;
  dra_disjoint : Disjoint dra_car;
  dra_op : Op dra_car;
  dra_valid : Valid dra_car;
  dra_mixin : DraMixin dra_car
}.
Arguments DraT _ {_ _ _ _ _} _.
Arguments dra_car : simpl never.
Arguments dra_equiv : simpl never.
Arguments dra_core : simpl never.
Arguments dra_disjoint : simpl never.
Arguments dra_op : simpl never.
Arguments dra_valid : simpl never.
Arguments dra_mixin : simpl never.
Add Printing Constructor draT.
Existing Instances dra_equiv dra_core dra_disjoint dra_op dra_valid.

(** Lifting properties from the mixin *)
Section dra_mixin.
  Context {A : draT}.
  Implicit Types x y : A.
  Global Instance dra_equivalence : Equivalence ((≡) : relation A).
  Proof. apply (mixin_dra_equivalence _ (dra_mixin A)). Qed.
  Global Instance dra_op_proper : Proper ((≡) ==> (≡) ==> (≡)) (@op A _).
  Proof. apply (mixin_dra_op_proper _ (dra_mixin A)). Qed.
  Global Instance dra_core_proper : Proper ((≡) ==> (≡)) (@core A _).
  Proof. apply (mixin_dra_core_proper _ (dra_mixin A)). Qed.
  Global Instance dra_valid_proper : Proper ((≡) ==> impl) (@valid A _).
  Proof. apply (mixin_dra_valid_proper _ (dra_mixin A)). Qed.
  Global Instance dra_disjoint_proper x : Proper ((≡) ==> impl) (disjoint x).
  Proof. apply (mixin_dra_disjoint_proper _ (dra_mixin A)). Qed.
  Lemma dra_op_valid x y : ✓ x → ✓ y → x ## y → ✓ (x ⋅ y).
  Proof. apply (mixin_dra_op_valid _ (dra_mixin A)). Qed.
  Lemma dra_core_valid x : ✓ x → ✓ core x.
  Proof. apply (mixin_dra_core_valid _ (dra_mixin A)). Qed.
  Lemma dra_assoc x y z :
    ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ⋅ (y ⋅ z) ≡ (x ⋅ y) ⋅ z.
  Proof. apply (mixin_dra_assoc _ (dra_mixin A)). Qed.
  Lemma dra_disjoint_ll x y z : ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## z.
  Proof. apply (mixin_dra_disjoint_ll _ (dra_mixin A)). Qed.
  Lemma dra_disjoint_move_l x y z :
    ✓ x → ✓ y → ✓ z → x ## y → x ⋅ y ## z → x ## y ⋅ z.
  Proof. apply (mixin_dra_disjoint_move_l _ (dra_mixin A)). Qed.
  Global Instance  dra_symmetric : Symmetric (@disjoint A _).
  Proof. apply (mixin_dra_symmetric _ (dra_mixin A)). Qed.
  Lemma dra_comm x y : ✓ x → ✓ y → x ## y → x ⋅ y ≡ y ⋅ x.
  Proof. apply (mixin_dra_comm _ (dra_mixin A)). Qed.
  Lemma dra_core_disjoint_l x : ✓ x → core x ## x.
  Proof. apply (mixin_dra_core_disjoint_l _ (dra_mixin A)). Qed.
  Lemma dra_core_l x : ✓ x → core x ⋅ x ≡ x.
  Proof. apply (mixin_dra_core_l _ (dra_mixin A)). Qed.
  Lemma dra_core_idemp x : ✓ x → core (core x) ≡ core x.
  Proof. apply (mixin_dra_core_idemp _ (dra_mixin A)). Qed.
  Lemma dra_core_mono x y : 
    ∃ z, ✓ x → ✓ y → x ## y → core (x ⋅ y) ≡ core x ⋅ z ∧ ✓ z ∧ core x ## z.
  Proof. apply (mixin_dra_core_mono _ (dra_mixin A)). Qed.
End dra_mixin.

Record validity (A : draT) := Validity {
  validity_car : A;
  validity_is_valid : Prop;
  validity_prf : validity_is_valid → valid validity_car
}.
Add Printing Constructor validity.
Arguments Validity {_} _ _ _.
Arguments validity_car {_} _.
Arguments validity_is_valid {_} _.

Definition to_validity {A : draT} (x : A) : validity A :=
  Validity x (valid x) id.

(* The actual construction *)
Section dra.
Context (A : draT).
Implicit Types a b : A.
Implicit Types x y z : validity A.
Arguments valid _ _ !_ /.

Instance validity_valid : Valid (validity A) := validity_is_valid.
Instance validity_equiv : Equiv (validity A) := λ x y,
  (valid x ↔ valid y) ∧ (valid x → validity_car x ≡ validity_car y).
Instance validity_equivalence : Equivalence (@equiv (validity A) _).
Proof.
  split; unfold equiv, validity_equiv.
  - by intros [x px ?]; simpl.
  - intros [x px ?] [y py ?]; naive_solver.
  - intros [x px ?] [y py ?] [z pz ?] [? Hxy] [? Hyz]; simpl in *.
    split; [|intros; trans y]; tauto.
Qed.
Canonical Structure validityC : ofeT := discreteC (validity A).

Instance dra_valid_proper' : Proper ((≡) ==> iff) (valid : A → Prop).
Proof. by split; apply: dra_valid_proper. Qed.
Global Instance to_validity_proper : Proper ((≡) ==> (≡)) to_validity.
Proof. by intros x1 x2 Hx; split; rewrite /= Hx. Qed.
Instance: Proper ((≡) ==> (≡) ==> iff) (disjoint : relation A).
Proof.
  intros x1 x2 Hx y1 y2 Hy; split.
  - by rewrite Hy (symmetry_iff (##) x1) (symmetry_iff (##) x2) Hx.
  - by rewrite -Hy (symmetry_iff (##) x2) (symmetry_iff (##) x1) -Hx.
Qed.

Lemma dra_disjoint_rl a b c : ✓ a → ✓ b → ✓ c → b ## c → a ## b ⋅ c → a ## b.
Proof. intros ???. rewrite !(symmetry_iff _ a). by apply dra_disjoint_ll. Qed.
Lemma dra_disjoint_lr a b c : ✓ a → ✓ b → ✓ c → a ## b → a ⋅ b ## c → b ## c.
Proof. intros ????. rewrite dra_comm //. by apply dra_disjoint_ll. Qed.
Lemma dra_disjoint_move_r a b c :
  ✓ a → ✓ b → ✓ c → b ## c → a ## b ⋅ c → a ⋅ b ## c.
Proof.
  intros; symmetry; rewrite dra_comm; eauto using dra_disjoint_rl.
  apply dra_disjoint_move_l; auto; by rewrite dra_comm.
Qed.
Hint Immediate dra_disjoint_move_l dra_disjoint_move_r.

Lemma validity_valid_car_valid z : ✓ z → ✓ validity_car z.
Proof. apply validity_prf. Qed.
Hint Resolve validity_valid_car_valid.
Program Instance validity_pcore : PCore (validity A) := λ x,
  Some (Validity (core (validity_car x)) (✓ x) _).
Solve Obligations with naive_solver eauto using dra_core_valid.
Program Instance validity_op : Op (validity A) := λ x y,
  Validity (validity_car x ⋅ validity_car y)
           (✓ x ∧ ✓ y ∧ validity_car x ## validity_car y) _.
Solve Obligations with naive_solver eauto using dra_op_valid.

Definition validity_ra_mixin : RAMixin (validity A).
Proof.
  apply ra_total_mixin; first eauto.
  - intros ??? [? Heq]; split; simpl; [|by intros (?&?&?); rewrite Heq].
    split; intros (?&?&?); split_and!;
      first [rewrite ?Heq; tauto|rewrite -?Heq; tauto|tauto].
  - by intros ?? [? Heq]; split; [done|]; simpl; intros ?; rewrite Heq.
  - intros ?? [??]; naive_solver.
  - intros [x px ?] [y py ?] [z pz ?]; split; simpl;
      [intuition eauto 2 using dra_disjoint_lr, dra_disjoint_rl
      |intuition eauto using dra_assoc, dra_disjoint_rl].
  - intros [x px ?] [y py ?]; split; naive_solver eauto using dra_comm.
  - intros [x px ?]; split;
      naive_solver eauto using dra_core_l, dra_core_disjoint_l.
  - intros [x px ?]; split; naive_solver eauto using dra_core_idemp.
  - intros [x px ?] [y py ?] [[z pz ?] [? Hy]]; simpl in *.
    destruct (dra_core_mono x z) as (z'&Hz').
    unshelve eexists (Validity z' (px ∧ py ∧ pz) _).
    { intros (?&?&?); apply Hz'; tauto. }
    split; simpl; first tauto.
    intros. rewrite Hy //. tauto.
  - by intros [x px ?] [y py ?] (?&?&?).
Qed.
Canonical Structure validityR : cmraT :=
  discreteR (validity A) validity_ra_mixin.

Global Instance validity_disrete_cmra : CmraDiscrete validityR.
Proof. apply discrete_cmra_discrete. Qed.
Global Instance validity_cmra_total : CmraTotal validityR.
Proof. rewrite /CmraTotal; eauto. Qed.

Lemma validity_update x y :
  (∀ c, ✓ x → ✓ c → validity_car x ## c → ✓ y ∧ validity_car y ## c) → x ~~> y.
Proof.
  intros Hxy; apply cmra_discrete_update=> z [?[??]].
  split_and!; try eapply Hxy; eauto.
Qed.

Lemma to_validity_op a b :
  (✓ (a ⋅ b) → ✓ a ∧ ✓ b ∧ a ## b) →
  to_validity (a ⋅ b) ≡ to_validity a ⋅ to_validity b.
Proof. split; naive_solver eauto using dra_op_valid. Qed.

(* TODO: This has to be proven again. *)
(*
Lemma to_validity_included x y:
  (✓ y ∧ to_validity x ≼ to_validity y)%stdpp ↔ (✓ x ∧ x ≼ y).
Proof.
  split.
  - move=>[Hvl [z [Hvxz EQ]]]. move:(Hvl)=>Hvl'. apply Hvxz in Hvl'.
    destruct Hvl' as [? [? ?]]; split; first done.
    exists (validity_car z); eauto.
  - intros (Hvl & z & EQ & ? & ?).
    assert (✓ y) by (rewrite EQ; by apply dra_op_valid).
    split; first done. exists (to_validity z). split; first split.
    + intros _. simpl. by split_and!.
    + intros _. setoid_subst. by apply dra_op_valid. 
    + intros _. rewrite /= EQ //.
Qed.
*)
End dra.
