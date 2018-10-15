From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export sts.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(** The CMRA we need. *)
Class stsG Σ (sts : stsT) := StsG {
  sts_inG :> inG Σ (stsR sts);
  sts_inhabited :> Inhabited (sts.state sts);
}.

Definition stsΣ (sts : stsT) : gFunctors := #[ GFunctor (stsR sts) ].
Instance subG_stsΣ Σ sts :
  subG (stsΣ sts) Σ → Inhabited (sts.state sts) → stsG Σ sts.
Proof. solve_inG. Qed.

Section definitions.
  Context `{stsG Σ sts} (γ : gname).

  Definition sts_ownS (S : sts.states sts) (T : sts.tokens sts) : iProp Σ :=
    own γ (sts_frag S T).
  Definition sts_own (s : sts.state sts) (T : sts.tokens sts) : iProp Σ :=
    own γ (sts_frag_up s T).
  Definition sts_inv (φ : sts.state sts → iProp Σ) : iProp Σ :=
    (∃ s, own γ (sts_auth s ∅) ∗ φ s)%I.
  Definition sts_ctx `{!invG Σ} (N : namespace) (φ: sts.state sts → iProp Σ) : iProp Σ :=
    inv N (sts_inv φ).

  Global Instance sts_inv_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_inv_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) sts_inv.
  Proof. solve_proper. Qed.
  Global Instance sts_ownS_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) sts_ownS.
  Proof. solve_proper. Qed.
  Global Instance sts_own_proper s : Proper ((≡) ==> (⊣⊢)) (sts_own s).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_ne `{!invG Σ} n N :
    Proper (pointwise_relation _ (dist n) ==> dist n) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_proper `{!invG Σ} N :
    Proper (pointwise_relation _ (≡) ==> (⊣⊢)) (sts_ctx N).
  Proof. solve_proper. Qed.
  Global Instance sts_ctx_persistent `{!invG Σ} N φ : Persistent (sts_ctx N φ).
  Proof. apply _. Qed.
  Global Instance sts_own_persistent s : Persistent (sts_own s ∅).
  Proof. apply _. Qed.
  Global Instance sts_ownS_persistent S : Persistent (sts_ownS S ∅).
  Proof. apply _. Qed.
End definitions.

Instance: Params (@sts_inv) 4.
Instance: Params (@sts_ownS) 4.
Instance: Params (@sts_own) 5.
Instance: Params (@sts_ctx) 6.

Section sts.
  Context `{invG Σ, stsG Σ sts}.
  Implicit Types φ : sts.state sts → iProp Σ.
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types γ : gname.
  Implicit Types S : sts.states sts.
  Implicit Types T : sts.tokens sts.

  (* The same rule as implication does *not* hold, as could be shown using
     sts_frag_included. *)
  Lemma sts_ownS_weaken γ S1 S2 T1 T2 :
    T2 ⊆ T1 → S1 ⊆ S2 → sts.closed S2 T2 →
    sts_ownS γ S1 T1 ==∗ sts_ownS γ S2 T2.
  Proof. intros ???. by apply own_update, sts_update_frag. Qed.

  Lemma sts_own_weaken γ s S T1 T2 :
    T2 ⊆ T1 → s ∈ S → sts.closed S T2 →
    sts_own γ s T1 ==∗ sts_ownS γ S T2.
  Proof. intros ???. by apply own_update, sts_update_frag_up. Qed.

  Lemma sts_own_weaken_state γ s1 s2 T :
    sts.frame_steps T s2 s1 → sts.tok s2 ## T →
    sts_own γ s1 T ==∗ sts_own γ s2 T.
  Proof.
    intros ??. apply own_update, sts_update_frag_up; [|done..].
    intros Hdisj. apply sts.closed_up. done. 
  Qed.

  Lemma sts_own_weaken_tok γ s T1 T2 :
    T2 ⊆ T1 → sts_own γ s T1 ==∗ sts_own γ s T2.
  Proof.
    intros ?. apply own_update, sts_update_frag_up; last done.
    - intros. apply sts.closed_up. set_solver.
    - apply sts.elem_of_up.
  Qed.

  Lemma sts_ownS_op γ S1 S2 T1 T2 :
    T1 ## T2 → sts.closed S1 T1 → sts.closed S2 T2 →
    sts_ownS γ (S1 ∩ S2) (T1 ∪ T2) ⊣⊢ (sts_ownS γ S1 T1 ∗ sts_ownS γ S2 T2).
  Proof. intros. by rewrite /sts_ownS -own_op sts_op_frag. Qed.

  Lemma sts_own_op γ s T1 T2 :
    T1 ## T2 → sts_own γ s (T1 ∪ T2) ==∗ sts_own γ s T1 ∗ sts_own γ s T2.
    (* The other direction does not hold -- see sts.up_op. *)
  Proof.
    intros. rewrite /sts_own -own_op. iIntros "Hown".
    iDestruct (own_valid with "Hown") as %Hval%sts_frag_up_valid.
    rewrite -sts_op_frag.
    - iApply (sts_own_weaken with "Hown"); first done.
      + split; apply sts.elem_of_up.
      + eapply sts.closed_op; apply sts.closed_up; set_solver.
    - done.
    - apply sts.closed_up; set_solver.
    - apply sts.closed_up; set_solver.
  Qed.

  Typeclasses Opaque sts_own sts_ownS sts_inv sts_ctx.

  Lemma sts_alloc φ E N s :
    ▷ φ s ={E}=∗ ∃ γ, sts_ctx γ N φ ∧ sts_own γ s (⊤ ∖ sts.tok s).
  Proof.
    iIntros "Hφ". rewrite /sts_ctx /sts_own.
    iMod (own_alloc (sts_auth s (⊤ ∖ sts.tok s))) as (γ) "Hγ".
    { apply sts_auth_valid; set_solver. }
    iExists γ; iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ $]".
    iMod (inv_alloc N _ (sts_inv γ φ) with "[Hφ Hγ]") as "#?"; auto.
    rewrite /sts_inv. iNext. iExists s. by iFrame.
  Qed.

  Lemma sts_accS φ E γ S T :
    ▷ sts_inv γ φ ∗ sts_ownS γ S T ={E}=∗ ∃ s,
      ⌜s ∈ S⌝ ∗ ▷ φ s ∗ ∀ s' T',
      ⌜sts.steps (s, T) (s', T')⌝ ∗ ▷ φ s' ={E}=∗ ▷ sts_inv γ φ ∗ sts_own γ s' T'.
  Proof.
    iIntros "[Hinv Hγf]". rewrite /sts_ownS /sts_inv /sts_own.
    iDestruct "Hinv" as (s) "[>Hγ Hφ]".
    iDestruct (own_valid_2 with "Hγ Hγf") as %Hvalid.
    assert (s ∈ S) by eauto using sts_auth_frag_valid_inv.
    assert (✓ sts_frag S T) as [??] by eauto using cmra_valid_op_r.
    iModIntro; iExists s; iSplit; [done|]; iFrame "Hφ".
    iIntros (s' T') "[% Hφ]".
    iMod (own_update_2 with "Hγ Hγf") as "Hγ".
    { rewrite sts_op_auth_frag; [|done..]. by apply sts_update_auth. }
    iRevert "Hγ"; rewrite -sts_op_auth_frag_up; iIntros "[Hγ $]".
    iModIntro. iNext. iExists s'; by iFrame.
  Qed.

  Lemma sts_acc φ E γ s0 T :
    ▷ sts_inv γ φ ∗ sts_own γ s0 T ={E}=∗ ∃ s,
      ⌜sts.frame_steps T s0 s⌝ ∗ ▷ φ s ∗ ∀ s' T',
      ⌜sts.steps (s, T) (s', T')⌝ ∗ ▷ φ s' ={E}=∗ ▷ sts_inv γ φ ∗ sts_own γ s' T'.
  Proof. by apply sts_accS. Qed.

  Lemma sts_openS φ E N γ S T :
    ↑N ⊆ E →
    sts_ctx γ N φ ∗ sts_ownS γ S T ={E,E∖↑N}=∗ ∃ s,
      ⌜s ∈ S⌝ ∗ ▷ φ s ∗ ∀ s' T',
      ⌜sts.steps (s, T) (s', T')⌝ ∗ ▷ φ s' ={E∖↑N,E}=∗ sts_own γ s' T'.
  Proof.
    iIntros (?) "[#? Hγf]". rewrite /sts_ctx. iInv N as "Hinv" "Hclose".
    (* The following is essentially a very trivial composition of the accessors
       [sts_acc] and [inv_open] -- but since we don't have any good support
       for that currently, this gets more tedious than it should, with us having
       to unpack and repack various proofs.
       TODO: Make this mostly automatic, by supporting "opening accessors
       around accessors". *)
    iMod (sts_accS with "[Hinv Hγf]") as (s) "(?&?& HclSts)"; first by iFrame.
    iModIntro. iExists s. iFrame. iIntros (s' T') "H".
    iMod ("HclSts" $! s' T' with "H") as "(Hinv & ?)". by iMod ("Hclose" with "Hinv").
  Qed.

  Lemma sts_open φ E N γ s0 T :
    ↑N ⊆ E →
    sts_ctx γ N φ ∗ sts_own γ s0 T ={E,E∖↑N}=∗ ∃ s,
      ⌜sts.frame_steps T s0 s⌝ ∗ ▷ φ s ∗ ∀ s' T',
      ⌜sts.steps (s, T) (s', T')⌝ ∗ ▷ φ s' ={E∖↑N,E}=∗ sts_own γ s' T'.
  Proof. by apply sts_openS. Qed.
End sts.

Typeclasses Opaque sts_own sts_ownS sts_inv sts_ctx.
