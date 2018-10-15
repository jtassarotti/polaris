From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".
Import uPred.

(** Least and greatest fixpoint of a monotone function, defined entirely inside
    the logic.  *)
Class BIMonoPred {M} {A : ofeT} (F : (A → uPred M) → (A → uPred M)) := {
  bi_mono_pred Φ Ψ : ((□ ∀ x, Φ x -∗ Ψ x) → ∀ x, F Φ x -∗ F Ψ x)%I;
  bi_mono_pred_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
}.
Arguments bi_mono_pred {_ _ _ _} _ _.
Local Existing Instance bi_mono_pred_ne.

Definition uPred_least_fixpoint {M} {A : ofeT}
    (F : (A → uPred M) → (A → uPred M)) (x : A) : uPred M :=
  (∀ Φ : A -n> uPredC M, □ (∀ x, F Φ x → Φ x) → Φ x)%I.

Definition uPred_greatest_fixpoint {M} {A : ofeT}
    (F : (A → uPred M) → (A → uPred M)) (x : A) : uPred M :=
  (∃ Φ : A -n> uPredC M, □ (∀ x, Φ x → F Φ x) ∧ Φ x)%I.

Section least.
  Context {M} {A : ofeT} (F : (A → uPred M) → (A → uPred M)) `{!BIMonoPred F}.

  Global Instance least_fixpoint_ne : NonExpansive (uPred_least_fixpoint F).
  Proof. solve_proper. Qed.

  Lemma least_fixpoint_unfold_2 x : F (uPred_least_fixpoint F) x ⊢ uPred_least_fixpoint F x.
  Proof.
    iIntros "HF" (Φ) "#Hincl".
    iApply "Hincl". iApply (bi_mono_pred _ Φ); last done.
    iIntros "!#" (y) "Hy". iApply "Hy". done.
  Qed.

  Lemma least_fixpoint_unfold_1 x :
    uPred_least_fixpoint F x ⊢ F (uPred_least_fixpoint F) x.
  Proof.
    iIntros "HF". iApply ("HF" $! (CofeMor (F (uPred_least_fixpoint F))) with "[#]").
    iIntros "!#" (y) "Hy". iApply bi_mono_pred; last done. iIntros "!#" (z) "?".
    by iApply least_fixpoint_unfold_2.
  Qed.

  Corollary least_fixpoint_unfold x :
    uPred_least_fixpoint F x ≡ F (uPred_least_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using least_fixpoint_unfold_1, least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_ind (Φ : A → uPred M) `{!NonExpansive Φ} :
    □ (∀ y, F Φ y → Φ y) ⊢ ∀ x, uPred_least_fixpoint F x → Φ x.
  Proof.
    iIntros "#HΦ" (x) "HF". by iApply ("HF" $! (CofeMor Φ) with "[#]").
  Qed.

  Lemma least_fixpoint_strong_ind (Φ : A → uPred M) `{!NonExpansive Φ} :
    □ (∀ y, F (λ x, Φ x ∧ uPred_least_fixpoint F x) y → Φ y)
    ⊢ ∀ x, uPred_least_fixpoint F x → Φ x.
  Proof.
    trans (∀ x, uPred_least_fixpoint F x → Φ x ∧ uPred_least_fixpoint F x)%I.
    { iIntros "#HΦ". iApply least_fixpoint_ind; first solve_proper.
      iIntros "!#" (y) "H". iSplit; first by iApply "HΦ".
      iApply least_fixpoint_unfold_2. iApply (bi_mono_pred with "[] H").
      by iIntros "!# * [_ ?]". }
    by setoid_rewrite and_elim_l.
  Qed.
End least.

Section greatest.
  Context {M} {A : ofeT} (F : (A → uPred M) → (A → uPred M)) `{!BIMonoPred F}.

  Global Instance greatest_fixpoint_ne : NonExpansive (uPred_greatest_fixpoint F).
  Proof. solve_proper. Qed.

  Lemma greatest_fixpoint_unfold_1 x :
    uPred_greatest_fixpoint F x ⊢ F (uPred_greatest_fixpoint F) x.
  Proof.
    iDestruct 1 as (Φ) "[#Hincl HΦ]".
    iApply (bi_mono_pred Φ (uPred_greatest_fixpoint F)).
    - iIntros "!#" (y) "Hy". iExists Φ. auto.
    - by iApply "Hincl".
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (uPred_greatest_fixpoint F) x ⊢ uPred_greatest_fixpoint F x.
  Proof.
    iIntros "HF". iExists (CofeMor (F (uPred_greatest_fixpoint F))).
    iIntros "{$HF} !#" (y) "Hy". iApply (bi_mono_pred with "[] Hy").
    iIntros "!#" (z) "?". by iApply greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    uPred_greatest_fixpoint F x ≡ F (uPred_greatest_fixpoint F) x.
  Proof.
    apply (anti_symm _); auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → uPred M) `{!NonExpansive Φ} :
    □ (∀ y, Φ y → F Φ y) ⊢ ∀ x, Φ x → uPred_greatest_fixpoint F x.
  Proof. iIntros "#HΦ" (x) "Hx". iExists (CofeMor Φ). by iIntros "{$Hx} !#". Qed.
End greatest.
