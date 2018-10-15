From iris.base_logic.lib Require Export invariants fractional.
From iris.algebra Require Export frac.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class cinvG Σ := cinv_inG :> inG Σ fracR.
Definition cinvΣ : gFunctors := #[GFunctor fracR].

Instance subG_cinvΣ {Σ} : subG cinvΣ Σ → cinvG Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{invG Σ, cinvG Σ}.

  Definition cinv_own (γ : gname) (p : frac) : iProp Σ := own γ p.

  Definition cinv (N : namespace) (γ : gname) (P : iProp Σ) : iProp Σ :=
    (∃ P', □ ▷ (P ↔ P') ∗ inv N (P' ∨ cinv_own γ 1%Qp))%I.
End defs.

Instance: Params (@cinv) 5.

Section proofs.
  Context `{invG Σ, cinvG Σ}.

  Global Instance cinv_own_timeless γ p : Timeless (cinv_own γ p).
  Proof. rewrite /cinv_own; apply _. Qed.

  Global Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. solve_contractive. Qed.
  Global Instance cinv_ne N γ : NonExpansive (cinv N γ).
  Proof. exact: contractive_ne. Qed.
  Global Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ).
  Proof. exact: ne_proper. Qed.

  Global Instance cinv_persistent N γ P : Persistent (cinv N γ P).
  Proof. rewrite /cinv; apply _. Qed.

  Global Instance cinv_own_fractionnal γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite -own_op. Qed.
  Global Instance cinv_own_as_fractionnal γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. split. done. apply _. Qed.

  Lemma cinv_own_valid γ q1 q2 : cinv_own γ q1 -∗ cinv_own γ q2 -∗ ✓ (q1 + q2)%Qp.
  Proof. apply (own_valid_2 γ q1 q2). Qed.

  Lemma cinv_own_1_l γ q : cinv_own γ 1 -∗ cinv_own γ q -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (cinv_own_valid with "H1 H2") as %[]%(exclusive_l 1%Qp).
  Qed.

  Lemma cinv_iff N γ P P' :
    ▷ □ (P ↔ P') -∗ cinv N γ P -∗ cinv N γ P'.
  Proof.
    iIntros "#HP' Hinv". iDestruct "Hinv" as (P'') "[#HP'' Hinv]".
    iExists _. iFrame "Hinv". iNext. iAlways. iSplit.
    - iIntros "?". iApply "HP''". iApply "HP'". done.
    - iIntros "?". iApply "HP'". iApply "HP''". done.
  Qed.

  Lemma cinv_alloc E N P : ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP".
    iMod (own_alloc 1%Qp) as (γ) "H1"; first done.
    iMod (inv_alloc N _ (P ∨ own γ 1%Qp)%I with "[HP]"); first by eauto.
    iExists _. iFrame. iExists _. iFrame. iIntros "!> !# !>". iSplit; by iIntros "?".
  Qed.

  Lemma cinv_cancel E N γ P : ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P.
  Proof.
    iIntros (?) "#Hinv Hγ". iDestruct "Hinv" as (P') "[#HP' Hinv]".
    iInv N as "[HP|>Hγ']" "Hclose".
    - iMod ("Hclose" with "[Hγ]") as "_"; first by eauto. iModIntro. iNext.
      iApply "HP'". done.
    - iDestruct (cinv_own_1_l with "Hγ Hγ'") as %[].
  Qed.

  Lemma cinv_open E N γ p P :
    ↑N ⊆ E →
    cinv N γ P -∗ cinv_own γ p ={E,E∖↑N}=∗ ▷ P ∗ cinv_own γ p ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?) "#Hinv Hγ". iDestruct "Hinv" as (P') "[#HP' Hinv]".
    iInv N as "[HP | >Hγ']" "Hclose".
    - iIntros "!> {$Hγ}". iSplitL "HP".
      + iNext. iApply "HP'". done.
      + iIntros "HP". iApply "Hclose". iLeft. iNext. by iApply "HP'".
    - iDestruct (cinv_own_1_l with "Hγ' Hγ") as %[].
  Qed.
End proofs.

Typeclasses Opaque cinv_own cinv.
