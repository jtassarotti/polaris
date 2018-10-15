(* This file shows that the fancy update can be encoded in terms of the
view shift, and that the laws of the fancy update can be derived from the
laws of the view shift. *)
From iris.proofmode Require Import tactics.
From stdpp Require Export coPset.
Set Default Proof Using "Type*".

Section fupd.
Context {M} (vs : coPset → coPset → uPred M → uPred M → uPred M).

Notation "P ={ E1 , E2 }=> Q" := (vs E1 E2 P Q)
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=>  Q") : uPred_scope.

Context (vs_ne : ∀ E1 E2, NonExpansive2 (vs E1 E2)).
Context (vs_persistent : ∀ E1 E2 P Q, Persistent (P ={E1,E2}=> Q)).

Context (vs_impl : ∀ E P Q, □ (P → Q) ⊢ P ={E,E}=> Q).
Context (vs_transitive : ∀ E1 E2 E3 P Q R,
  (P ={E1,E2}=> Q) ∧ (Q ={E2,E3}=> R) ⊢ P ={E1,E3}=> R).
Context (vs_mask_frame_r : ∀ E1 E2 Ef P Q,
  E1 ## Ef → (P ={E1,E2}=> Q) ⊢ P ={E1 ∪ Ef,E2 ∪ Ef}=> Q).
Context (vs_frame_r : ∀ E1 E2 P Q R, (P ={E1,E2}=> Q) ⊢ P ∗ R ={E1,E2}=> Q ∗ R).
Context (vs_exists : ∀ {A} E1 E2 (Φ : A → uPred M) Q,
  (∀ x, Φ x ={E1,E2}=> Q) ⊢ (∃ x, Φ x) ={E1,E2}=> Q).
Context (vs_persistent_intro_r : ∀ E1 E2 P Q R,
  Persistent R →
  (R -∗ (P ={E1,E2}=> Q)) ⊢ P ∗ R ={E1,E2}=> Q).

Definition fupd (E1 E2 : coPset) (P : uPred M) : uPred M :=
  (∃ R, R ∗ vs E1 E2 R P)%I.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : uPred_scope.

Global Instance fupd_ne E1 E2 : NonExpansive (@fupd E1 E2).
Proof. solve_proper. Qed.

Lemma fupd_intro E P : P ⊢ |={E,E}=> P.
Proof. iIntros "HP". iExists P. iFrame "HP". iApply vs_impl; auto. Qed.

Lemma fupd_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
Proof.
  iIntros (HPQ); iDestruct 1 as (R) "[HR Hvs]".
  iExists R; iFrame "HR". iApply (vs_transitive with "[$Hvs]").
  iApply vs_impl. iIntros "!# HP". by iApply HPQ.
Qed.

Lemma fupd_trans E1 E2 E3 P : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
Proof.
  iDestruct 1 as (R) "[HR Hvs]". iExists R. iFrame "HR".
  iApply (vs_transitive with "[$Hvs]"). clear R.
  iApply vs_exists; iIntros (R). iApply vs_persistent_intro_r; iIntros "Hvs".
  iApply (vs_transitive with "[$Hvs]"). iApply vs_impl; auto.
Qed.

Lemma fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → (|={E1,E2}=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}=> P.
Proof.
  iIntros (HE); iDestruct 1 as (R) "[HR Hvs]". iExists R; iFrame "HR".
  by iApply vs_mask_frame_r.
Qed.

Lemma fupd_frame_r E1 E2 P Q : (|={E1,E2}=> P) ∗ Q ⊢ |={E1,E2}=> P ∗ Q.
Proof.
  iIntros "[Hvs HQ]". iDestruct "Hvs" as (R) "[HR Hvs]".
  iExists (R ∗ Q)%I. iFrame "HR HQ". by iApply vs_frame_r.
Qed.
End fupd.