From iris.algebra Require Export cmra.
From iris.algebra Require Import updates.
From stdpp Require Import finite.
Set Default Proof Using "Type".

Definition ofe_fun_insert `{EqDecision A} {B : A → ofeT}
    (x : A) (y : B x) (f : ofe_fun B) : ofe_fun B := λ x',
  match decide (x = x') with left H => eq_rect _ B y _ H | right _ => f x' end.
Instance: Params (@ofe_fun_insert) 5.

Definition ofe_fun_singleton `{EqDecision A} {B : A → ucmraT}
  (x : A) (y : B x) : ofe_fun B := ofe_fun_insert x y ε.
Instance: Params (@ofe_fun_singleton) 5.

Section ofe.
  Context `{Heqdec : EqDecision A} {B : A → ofeT}.
  Implicit Types x : A.
  Implicit Types f g : ofe_fun B.

  (** Properties of ofe_fun_insert. *)
  Global Instance ofe_fun_insert_ne x :
    NonExpansive2 (ofe_fun_insert (B:=B) x).
  Proof.
    intros n y1 y2 ? f1 f2 ? x'; rewrite /ofe_fun_insert.
    by destruct (decide _) as [[]|].
  Qed.
  Global Instance ofe_fun_insert_proper x :
    Proper ((≡) ==> (≡) ==> (≡)) (ofe_fun_insert (B:=B) x) := ne_proper_2 _.

  Lemma ofe_fun_lookup_insert f x y : (ofe_fun_insert x y f) x = y.
  Proof.
    rewrite /ofe_fun_insert; destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
  Lemma ofe_fun_lookup_insert_ne f x x' y :
    x ≠ x' → (ofe_fun_insert x y f) x' = f x'.
  Proof. by rewrite /ofe_fun_insert; destruct (decide _). Qed.

  Global Instance ofe_fun_insert_discrete f x y :
    Discrete f → Discrete y → Discrete (ofe_fun_insert x y f).
  Proof.
    intros ?? g Heq x'; destruct (decide (x = x')) as [->|].
    - rewrite ofe_fun_lookup_insert.
      apply: discrete. by rewrite -(Heq x') ofe_fun_lookup_insert.
    - rewrite ofe_fun_lookup_insert_ne //.
      apply: discrete. by rewrite -(Heq x') ofe_fun_lookup_insert_ne.
  Qed.
End ofe.

Section cmra.
  Context `{EqDecision A} {B : A → ucmraT}.
  Implicit Types x : A.
  Implicit Types f g : ofe_fun B.

  Global Instance ofe_fun_singleton_ne x :
    NonExpansive (ofe_fun_singleton x : B x → _).
  Proof. intros n y1 y2 ?; apply ofe_fun_insert_ne. done. by apply equiv_dist. Qed.
  Global Instance ofe_fun_singleton_proper x :
    Proper ((≡) ==> (≡)) (ofe_fun_singleton x) := ne_proper _.

  Lemma ofe_fun_lookup_singleton x (y : B x) : (ofe_fun_singleton x y) x = y.
  Proof. by rewrite /ofe_fun_singleton ofe_fun_lookup_insert. Qed.
  Lemma ofe_fun_lookup_singleton_ne x x' (y : B x) :
    x ≠ x' → (ofe_fun_singleton x y) x' = ε.
  Proof. intros; by rewrite /ofe_fun_singleton ofe_fun_lookup_insert_ne. Qed.

  Global Instance ofe_fun_singleton_discrete x (y : B x) :
    (∀ i, Discrete (ε : B i)) →  Discrete y → Discrete (ofe_fun_singleton x y).
  Proof. apply _. Qed.

  Lemma ofe_fun_singleton_validN n x (y : B x) : ✓{n} ofe_fun_singleton x y ↔ ✓{n} y.
  Proof.
    split; [by move=>/(_ x); rewrite ofe_fun_lookup_singleton|].
    move=>Hx x'; destruct (decide (x = x')) as [->|];
      rewrite ?ofe_fun_lookup_singleton ?ofe_fun_lookup_singleton_ne //.
    by apply ucmra_unit_validN.
  Qed.

  Lemma ofe_fun_core_singleton x (y : B x) :
    core (ofe_fun_singleton x y) ≡ ofe_fun_singleton x (core y).
  Proof.
    move=>x'; destruct (decide (x = x')) as [->|];
      by rewrite ofe_fun_lookup_core ?ofe_fun_lookup_singleton
      ?ofe_fun_lookup_singleton_ne // (core_id_core ∅).
  Qed.

  Global Instance ofe_fun_singleton_core_id x (y : B x) :
    CoreId y → CoreId (ofe_fun_singleton x y).
  Proof. by rewrite !core_id_total ofe_fun_core_singleton=> ->. Qed.

  Lemma ofe_fun_op_singleton (x : A) (y1 y2 : B x) :
    ofe_fun_singleton x y1 ⋅ ofe_fun_singleton x y2 ≡ ofe_fun_singleton x (y1 ⋅ y2).
  Proof.
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite ofe_fun_lookup_op !ofe_fun_lookup_singleton.
    - by rewrite ofe_fun_lookup_op !ofe_fun_lookup_singleton_ne // left_id.
  Qed.

  Lemma ofe_fun_insert_updateP x (P : B x → Prop) (Q : ofe_fun B → Prop) g y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (ofe_fun_insert x y2 g)) →
    ofe_fun_insert x y1 g ~~>: Q.
  Proof.
    intros Hy1 HP; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hy1 n (Some (gf x))) as (y2&?&?).
    { move: (Hg x). by rewrite ofe_fun_lookup_op ofe_fun_lookup_insert. }
    exists (ofe_fun_insert x y2 g); split; [auto|].
    intros x'; destruct (decide (x' = x)) as [->|];
      rewrite ofe_fun_lookup_op ?ofe_fun_lookup_insert //; [].
    move: (Hg x'). by rewrite ofe_fun_lookup_op !ofe_fun_lookup_insert_ne.
  Qed.

  Lemma ofe_fun_insert_updateP' x (P : B x → Prop) g y1 :
    y1 ~~>: P →
    ofe_fun_insert x y1 g ~~>: λ g', ∃ y2, g' = ofe_fun_insert x y2 g ∧ P y2.
  Proof. eauto using ofe_fun_insert_updateP. Qed.
  Lemma ofe_fun_insert_update g x y1 y2 :
    y1 ~~> y2 → ofe_fun_insert x y1 g ~~> ofe_fun_insert x y2 g.
  Proof.
    rewrite !cmra_update_updateP; eauto using ofe_fun_insert_updateP with subst.
  Qed.

  Lemma ofe_fun_singleton_updateP x (P : B x → Prop) (Q : ofe_fun B → Prop) y1 :
    y1 ~~>: P → (∀ y2, P y2 → Q (ofe_fun_singleton x y2)) →
    ofe_fun_singleton x y1 ~~>: Q.
  Proof. rewrite /ofe_fun_singleton; eauto using ofe_fun_insert_updateP. Qed.
  Lemma ofe_fun_singleton_updateP' x (P : B x → Prop) y1 :
    y1 ~~>: P →
    ofe_fun_singleton x y1 ~~>: λ g, ∃ y2, g = ofe_fun_singleton x y2 ∧ P y2.
  Proof. eauto using ofe_fun_singleton_updateP. Qed.
  Lemma ofe_fun_singleton_update x (y1 y2 : B x) :
    y1 ~~> y2 → ofe_fun_singleton x y1 ~~> ofe_fun_singleton x y2.
  Proof. eauto using ofe_fun_insert_update. Qed.

  Lemma ofe_fun_singleton_updateP_empty x (P : B x → Prop) (Q : ofe_fun B → Prop) :
    ε ~~>: P → (∀ y2, P y2 → Q (ofe_fun_singleton x y2)) → ε ~~>: Q.
  Proof.
    intros Hx HQ; apply cmra_total_updateP.
    intros n gf Hg. destruct (Hx n (Some (gf x))) as (y2&?&?); first apply Hg.
    exists (ofe_fun_singleton x y2); split; [by apply HQ|].
    intros x'; destruct (decide (x' = x)) as [->|].
    - by rewrite ofe_fun_lookup_op ofe_fun_lookup_singleton.
    - rewrite ofe_fun_lookup_op ofe_fun_lookup_singleton_ne //. apply Hg.
  Qed.
  Lemma ofe_fun_singleton_updateP_empty' x (P : B x → Prop) :
    ε ~~>: P → ε ~~>: λ g, ∃ y2, g = ofe_fun_singleton x y2 ∧ P y2.
  Proof. eauto using ofe_fun_singleton_updateP_empty. Qed.
  Lemma ofe_fun_singleton_update_empty x (y : B x) :
    ε ~~> y → ε ~~> ofe_fun_singleton x y.
  Proof.
    rewrite !cmra_update_updateP;
      eauto using ofe_fun_singleton_updateP_empty with subst.
  Qed.
End cmra.
