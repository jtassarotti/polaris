From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** The "core" of an assertion is its maximal persistent part. *)
Definition coreP {M : ucmraT} (P : uPred M) : uPred M :=
  (∀ Q, ■ (Q → □ Q) → ■ (P → Q) → Q)%I.
Instance: Params (@coreP) 1.
Typeclasses Opaque coreP.

Section core.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.

  Lemma coreP_intro P : P -∗ coreP P.
  Proof. rewrite /coreP. iIntros "HP" (Q) "_ HPQ". by iApply "HPQ". Qed.

  Global Instance coreP_persistent P : Persistent (coreP P).
  Proof.
    rewrite /coreP /Persistent. iIntros "HC" (Q).
    iApply persistently_impl_plainly. iIntros "#HQ".
    iApply persistently_impl_plainly. iIntros "#HPQ".
    iApply "HQ". by iApply "HC".
  Qed.

  Global Instance coreP_ne : NonExpansive (@coreP M).
  Proof. solve_proper. Qed.
  Global Instance coreP_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@coreP M).
  Proof. solve_proper. Qed.

  Global Instance coreP_mono : Proper ((⊢) ==> (⊢)) (@coreP M).
  Proof.
    rewrite /coreP. iIntros (P P' HP) "H"; iIntros (Q) "#HQ #HPQ".
    iApply ("H" $! Q with "[]"); first done. by rewrite HP.
  Qed.

  Lemma coreP_elim P : Persistent P → coreP P -∗ P.
  Proof. rewrite /coreP. iIntros (?) "HCP". iApply ("HCP" $! P); auto. Qed.

  Lemma coreP_wand P Q : (coreP P ⊢ Q) ↔ (P ⊢ □ Q).
  Proof.
    split.
    - iIntros (HP) "HP". iDestruct (coreP_intro with "HP") as "#HcP".
      iAlways. by iApply HP.
    - iIntros (HPQ) "HcP". iDestruct (coreP_mono _ _ HPQ with "HcP") as "HcQ".
      iDestruct (coreP_elim with "HcQ") as "#HQ". done.
  Qed.
End core.
