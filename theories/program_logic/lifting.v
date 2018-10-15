From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∀ σ1 c1, state_interp σ1 ∗ aux_interp c1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∃ c2, ∀ e2 σ2 efs c3,
      ⌜prim_step e1 σ1 e2 σ2 efs⌝  ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
      step_interpR e1 σ1 c1 c2 e2 σ2 efs c3 ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. by rewrite wp_unfold /wp_pre=> ->. Qed.

Lemma wp_lift_stuck E Φ e :
  to_val e = None →
  (∀ σ c1, state_interp σ ∗ aux_interp c1 ={E,∅}=∗ ∃ c2 : choice_type e σ c1, ⌜stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->. iIntros "H" (σ1 c1) "Hσ".
  iMod ("H" with "Hσ") as %[c2 [? Hirr]]. iModIntro. iSplit; first done.
  iExists c2.
  iIntros "!>" (e2 σ2 efs) "% %". by case: (Hirr e2 σ2 efs).
Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_pure_step `{Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (∀ σ c1, aux_interp c1 ={E,E'}=∗ ▷(∃ c2, (|={E',E}=>
    ∀ e2 efs c3, ⌜prim_step e1 σ e2 σ efs⌝ -∗
    WP e2 @ s; E {{ Φ }} ∗
    step_interpR e1 σ c1 c2 e2 σ efs c3 ∗
    [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; last done.
      by eapply reducible_not_val. }
  iIntros (σ1 c1) "(Hσ&Ha)". iMod ("H" with "Ha") as "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iDestruct "H" as (c2) "H".
  iExists c2. iIntros (e2 σ2 efs c3) "%".
  destruct (Hstep σ1 e2 σ2 efs); auto; subst.
  iMod "Hclose" as "_". iFrame "Hσ". iMod "H". iApply "H"; auto.
Qed.

Lemma wp_lift_pure_stuck `{Inhabited (state Λ)} `{Inhabited aux_state} E Φ e :
  (∀ σ, stuck e σ) →
  (∀ σ c1, ∃ c : choice_type e σ c1, True) →
  True ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck Hchoice) "_". iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (σ c1) "_". iMod (fupd_intro_mask' E ∅) as "_".
    by set_solver. iModIntro. iPureIntro. destruct (Hchoice σ c1). eexists; eauto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 c1, state_interp σ1 ∗ aux_interp c1 ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∃ c2, ∀ e2 σ2 efs c3, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗
      step_interpR e1 σ1 c1 c2 e2 σ2 efs c3 ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step s E _ e1)=>//; iIntros (σ1 c1) "Hσ1".
  iMod ("H" $! σ1 c1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro; iNext.
  iDestruct "H" as (c2) "H".
  iExists c2.
  iIntros (e2 σ2 efs c3) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs c3 with "[%]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step `{Inhabited (state Λ)} {s E E' Φ} e1 e2 efs :
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (∀ σ c1, aux_interp c1 ={E, E'}=∗ ▷(∃ c2,  (|={E',E}=> ∀ c3, WP e2 @ s; E {{ Φ }} ∗ step_interpR e1 σ c1 c2 e2 σ efs c3 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E E'); try done.
  { by intros; eapply Hpuredet. }
  iIntros (σ1 c1) "Ha".
  iSpecialize ("H" with "Ha").
  iMod ("H"). 
  iModIntro. iNext.
  iDestruct "H" as (c2) "H".
  iExists c2. iMod "H". iModIntro.
  iIntros.
  edestruct Hpuredet as (_&->&->); first by eauto.
  by iApply "H".
Qed.

End lifting.
