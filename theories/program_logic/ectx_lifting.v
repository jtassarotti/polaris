(** Some derived lemmas for ectx-based languages *)
From iris.program_logic Require Export prob_language ectx_language weakestpre lifting.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section wp.
Context {Λ : ectxLanguage} `{irisG Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Extern 2 (reducible ?e1 ?σ1) => apply head_prim_reducible.
Hint Extern 2 (head_step ?e1 ?σ1 ?e2 ?σ2 ?efs) => apply head_reducible_prim_step. 
Hint Extern 2 (stuck _ _) => apply head_stuck_stuck.
Hint Extern 2 (language.to_val _ = None) => apply (reducible_not_val _ inhabitant).
(*
Hint Resolve (reducible_not_val _ inhabitant).
Hint Resolve head_stuck_stuck.
*)


Lemma wp_ectx_bind {E Φ} K e 
      (HfillR: ∀ e1 σ1 c1 c2 K, ∃ c2', ∀ e2 σ2 efs r', ∃ r,
          (step_interpR e1 σ1 c1 c2 e2 σ2 efs r ⊢ step_interpR (K e1) σ1 c1 c2' (K e2) σ2 efs r')):
  WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }} ⊢ WP fill K e @ E {{ Φ }}.
Proof. by apply: weakestpre.wp_bind. Qed.

(*
Lemma wp_ectx_bind_inv {E Φ} K e :
  WP fill K e @ E {{ Φ }} ⊢ WP e @ E {{ v, WP fill K (of_val v) @ E {{ Φ }} }}.
Proof. apply: weakestpre.wp_bind_inv. Qed.
*)

Lemma wp_lift_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 c1, state_interp σ1 ∗ aux_interp c1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∃ c2, ∀ e2 σ2 efs c3, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
      step_interpR e1 σ1 c1 c2 e2 σ2 efs c3 ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step s E)=>//. iIntros (σ1 c1) "Hσ".
  iMod ("H" $! σ1 with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by destruct s; eauto. iNext.
  iDestruct "H" as (c) "H". iExists c.
  iIntros (e2 σ2 efs c3) "%".
  iApply "H". by eauto.
Qed.

Lemma wp_lift_head_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ c1, state_interp σ ∗ aux_interp c1 ={E,∅}=∗ ∃ _ : choice_type e σ c1, ⌜head_stuck e σ⌝)
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply wp_lift_stuck; first done.
  iIntros (σ c1) "Hσ". iMod ("H" with "Hσ") as %[c2 ?]. iExists c2; eauto. 
Qed.

Lemma wp_lift_pure_head_step {s E E' Φ} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (∀ σ c1, aux_interp c1 ={E, E'}=∗ ▷(∃ c2, (|={E',E}=> ∀ e2 efs c3, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E {{ Φ }} ∗
    step_interpR e1 σ c1 c2 e2 σ efs c3 ∗
    [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})))
  ⊢ WP e1 @ s ; E {{ Φ }}.
Proof using Hinh.
  iIntros (??) "H". iApply wp_lift_pure_step; [ eauto | eauto | ].
  { by destruct s; auto. }
  iIntros (σ c1) "Ha". iMod ("H" with "Ha") as "H".
  iModIntro; iNext.
  iDestruct "H" as (c2) "H".
  iExists c2. iMod "H". iModIntro.
  iIntros. iApply "H". 
  eauto.
Qed.

Lemma wp_lift_pure_head_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, head_stuck e σ) →
  (∀ σ c1, ∃ c2: choice_type e σ c1, True) →
  WP e @ E ?{{ Φ }}%I.
Proof using Hinh.
  iIntros (?? Hstuck Hchoice). iApply wp_lift_head_stuck; [done|done|].
  iIntros (σ c1) "_". iMod (fupd_intro_mask' E ∅) as "_"; first set_solver.
  iPureIntro. edestruct (Hchoice) as (c2&?). eexists; eauto.
Qed.

Lemma wp_lift_atomic_head_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 c1, state_interp σ1 ∗ aux_interp c1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∃ c2, ∀ e2 σ2 efs c3, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗
      step_interpR e1 σ1 c1 c2 e2 σ2 efs c3 ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (σ1 c1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext.
  iDestruct "H" as (c) "H".
  iExists c. iIntros (e2 σ2 efs c3) "%". iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1 c1, state_interp σ1 ∗ aux_interp c1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
     ▷ (∃ c2, ∀ e2 σ2 efs c3, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ ∗
      step_interpR e1 σ1 c1 c2 e2 σ2 efs c3))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1 c1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iDestruct "H" as (c) "H"; iExists c; iIntros (v2 σ2 efs c3) "%".
  iMod ("H" $! v2 σ2 efs c3 with "[# //]") as "(% & $ & $ & ?)"; subst; auto.
Qed.

Lemma wp_lift_pure_det_head_step {s E E' Φ} e1 e2 efs :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (∀ σ1 c1, aux_interp c1 ={E, E'}=∗ ▷(∃ c2, (|={E',E}=> ∀ c3, WP e2 @ s; E {{ Φ }} ∗ step_interpR e1 σ1  c1 c2 e2 σ1 efs c3 ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 efs); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  (∀ σ1 c1, aux_interp c1 ={E, E'}=∗
    ▷(∃ c2, (|={E',E}=> ∀ c3, WP e2 @ s; E {{ Φ }} ∗ step_interpR e1 σ1 c1 c2 e2 σ1 [] c3)))
    ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step e1 e2 []) /= ?right_id; eauto;
            last by destruct s; eauto.
  iIntros "H".
  iIntros (σ1 c1) "Hσ1". iMod ("H" $! σ1 c1 with "Hσ1") as "H". 
  iModIntro.
  iNext; iDestruct "H" as (c2) "H"; iExists c2.
  iMod "H". iModIntro.
  iIntros (c3). iDestruct ("H" $! c3) as "($&$)".
Qed.

(*
Lemma wp_lift_pure_det_head_step_no_fork' {E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ [] = efs') →
  ▷ (∀ σ c1, aux_inter ∃ c2, ∀ σ, WP e2 @ E {{ Φ }} ∗ step_interp e1 σ e2 σ [] choice)  ⊢ WP e1 @ E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_ex_intro //.
Qed.
*)
End wp.
