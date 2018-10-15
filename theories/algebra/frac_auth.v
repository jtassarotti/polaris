From iris.algebra Require Export frac auth.
From iris.algebra Require Export updates local_updates.
From iris.proofmode Require Import classes.

Definition frac_authR (A : cmraT) : cmraT :=
  authR (optionUR (prodR fracR A)).
Definition frac_authUR (A : cmraT) : ucmraT :=
  authUR (optionUR (prodR fracR A)).

Definition frac_auth_auth {A : cmraT} (x : A) : frac_authR A :=
  ● (Some (1%Qp,x)).
Definition frac_auth_frag {A : cmraT} (q : frac) (x : A) : frac_authR A :=
  ◯ (Some (q,x)).

Typeclasses Opaque frac_auth_auth frac_auth_frag.

Instance: Params (@frac_auth_auth) 1.
Instance: Params (@frac_auth_frag) 2.

Notation "●! a" := (frac_auth_auth a) (at level 10).
Notation "◯!{ q } a" := (frac_auth_frag q a) (at level 10, format "◯!{ q }  a").
Notation "◯! a" := (frac_auth_frag 1 a) (at level 10).

Section frac_auth.
  Context {A : cmraT}.
  Implicit Types a b : A.

  Global Instance frac_auth_auth_ne : NonExpansive (@frac_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_auth_proper : Proper ((≡) ==> (≡)) (@frac_auth_auth A).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_ne q : NonExpansive (@frac_auth_frag A q).
  Proof. solve_proper. Qed.
  Global Instance frac_auth_frag_proper q : Proper ((≡) ==> (≡)) (@frac_auth_frag A q).
  Proof. solve_proper. Qed.

  Global Instance frac_auth_auth_discrete a : Discrete a → Discrete (●! a).
  Proof. intros; apply Auth_discrete; apply _. Qed.
  Global Instance frac_auth_frag_discrete a : Discrete a → Discrete (◯! a).
  Proof. intros; apply Auth_discrete, Some_discrete; apply _. Qed.

  Lemma frac_auth_validN n a : ✓{n} a → ✓{n} (●! a ⋅ ◯! a).
  Proof. done. Qed.
  Lemma frac_auth_valid a : ✓ a → ✓ (●! a ⋅ ◯! a).
  Proof. done. Qed.

  Lemma frac_auth_agreeN n a b : ✓{n} (●! a ⋅ ◯! b) → a ≡{n}≡ b.
  Proof.
    rewrite auth_validN_eq /= => -[Hincl Hvalid].
    by move: Hincl=> /Some_includedN_exclusive /(_ Hvalid ) [??].
  Qed.
  Lemma frac_auth_agree a b : ✓ (●! a ⋅ ◯! b) → a ≡ b.
  Proof.
    intros. apply equiv_dist=> n. by apply frac_auth_agreeN, cmra_valid_validN.
  Qed.
  Lemma frac_auth_agreeL `{!LeibnizEquiv A} a b : ✓ (●! a ⋅ ◯! b) → a = b.
  Proof. intros. by apply leibniz_equiv, frac_auth_agree. Qed.

  Lemma frac_auth_includedN n q a b : ✓{n} (●! a ⋅ ◯!{q} b) → Some b ≼{n} Some a.
  Proof. by rewrite auth_validN_eq /= => -[/Some_pair_includedN [_ ?] _]. Qed.
  Lemma frac_auth_included `{CmraDiscrete A} q a b :
    ✓ (●! a ⋅ ◯!{q} b) → Some b ≼ Some a.
  Proof. by rewrite auth_valid_discrete /= => -[/Some_pair_included [_ ?] _]. Qed.
  Lemma frac_auth_includedN_total `{CmraTotal A} n q a b :
    ✓{n} (●! a ⋅ ◯!{q} b) → b ≼{n} a.
  Proof. intros. by eapply Some_includedN_total, frac_auth_includedN. Qed.
  Lemma frac_auth_included_total `{CmraDiscrete A, CmraTotal A} q a b :
    ✓ (●! a ⋅ ◯!{q} b) → b ≼ a.
  Proof. intros. by eapply Some_included_total, frac_auth_included. Qed.

  Lemma frac_auth_auth_validN n a : ✓{n} (●! a) ↔ ✓{n} a.
  Proof.
    split; [by intros [_ [??]]|].
    by repeat split; simpl; auto using ucmra_unit_leastN.
  Qed.
  Lemma frac_auth_auth_valid a : ✓ (●! a) ↔ ✓ a.
  Proof. rewrite !cmra_valid_validN. by setoid_rewrite frac_auth_auth_validN. Qed.

  Lemma frac_auth_frag_validN n q a : ✓{n} (◯!{q} a) ↔ ✓{n} q ∧ ✓{n} a.
  Proof. done. Qed.
  Lemma frac_auth_frag_valid q a : ✓ (◯!{q} a) ↔ ✓ q ∧ ✓ a.
  Proof. done. Qed.

  Lemma frag_auth_op q1 q2 a1 a2 : ◯!{q1+q2} (a1 ⋅ a2) ≡ ◯!{q1} a1 ⋅ ◯!{q2} a2.
  Proof. done. Qed.

  Lemma frac_auth_frag_validN_op_1_l n q a b : ✓{n} (◯!{1} a ⋅ ◯!{q} b) → False.
  Proof. rewrite -frag_auth_op frac_auth_frag_validN=> -[/exclusiveN_l []]. Qed.
  Lemma frac_auth_frag_valid_op_1_l q a b : ✓ (◯!{1} a ⋅ ◯!{q} b) → False.
  Proof. rewrite -frag_auth_op frac_auth_frag_valid=> -[/exclusive_l []]. Qed.

  Global Instance is_op_frac_auth (q q1 q2 : frac) (a a1 a2 : A) :
    IsOp q q1 q2 → IsOp a a1 a2 → IsOp' (◯!{q} a) (◯!{q1} a1) (◯!{q2} a2).
  Proof. by rewrite /IsOp' /IsOp=> /leibniz_equiv_iff -> ->. Qed.

  Global Instance is_op_frac_auth_core_id (q q1 q2 : frac) (a  : A) :
    CoreId a → IsOp q q1 q2 → IsOp' (◯!{q} a) (◯!{q1} a) (◯!{q2} a).
  Proof.
    rewrite /IsOp' /IsOp=> ? /leibniz_equiv_iff ->.
    by rewrite -frag_auth_op -core_id_dup.
  Qed.

  Lemma frac_auth_update q a b a' b' :
    (a,b) ~l~> (a',b') → ●! a ⋅ ◯!{q} b ~~> ●! a' ⋅ ◯!{q} b'.
  Proof.
    intros. by apply auth_update, option_local_update, prod_local_update_2.
  Qed.
End frac_auth.
