From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op soundness.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Global functor setup *)
Definition invΣ : gFunctors :=
  #[GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
    GFunctor coPset_disjUR;
    GFunctor (gset_disjUR positive)].

Class invPreG (Σ : gFunctors) : Set := WsatPreG {
  inv_inPreG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inPreG :> inG Σ coPset_disjR;
  disabled_inPreG :> inG Σ (gset_disjR positive);
}.

Instance subG_invΣ {Σ} : subG invΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

(* Allocation *)
Lemma wsat_alloc `{invPreG Σ} : (|==> ∃ _ : invG Σ, wsat ∗ ownE ⊤)%I.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap _ _))) as (γI) "HI"; first done.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ _ _ γI γE γD).
  rewrite /wsat /ownE -lock; iFrame.
  iExists ∅. rewrite fmap_empty big_opM_empty. by iFrame.
Qed.

(* Program logic adequacy *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ) (φ : val Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ _, True }})%I.

Lemma wp_step s E e1 σ1 c1 e2 σ2 efs Φ:
  prim_step e1 σ1 e2 σ2 efs →
  state_interp σ1 ∗ WP e1 @ s; E {{ Φ }} ∗ aux_interp c1 ==∗
              |={E, ∅}▷=> ∃ c2, (state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗ wptp s efs ∗ aux_interp c2).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?). iIntros "(Hσ&H&Ha)".
  rewrite (val_stuck e1 σ1 e2 σ2 efs) //.
  iModIntro.
  iMod ("H" $! σ1 c1 with "[$Hσ $Ha]") as "(_&H)".
  iModIntro. iNext.
  iDestruct "H" as (c2) "H". 
  specialize (response_inhabited _ _ c1 c2 _ _ _ H) => c3.
  iMod ("H" $! e2 σ2 efs c3 with "[// ]") as "(?&?&Hs&?)". 
  iMod (step_to_aux with "Hs") as (c1') "H".
  iExists c1'. iModIntro. iFrame.
Qed.

Lemma wptp_step s e1 t1 t2 σ1 σ2 c1 Φ :
  step (e1 :: t1,σ1) (t2, σ2) →
  state_interp σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ∗ aux_interp c1
        ==∗ ∃ e2 t2', ⌜t2 = e2 :: t2'⌝
             ∗ |={⊤, ∅}▷=> ∃ c2, (state_interp σ2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2' ∗ aux_interp c2).
Proof .
  iIntros (Hstep) "(HW & He & Ht & Hsl)".
  destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', (t2' ++ efs); iSplitR; first eauto.
    iFrame "Ht".  iApply wp_step; eauto. iFrame.
  - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
    iDestruct "Ht" as "($ & He' & $)". iFrame "He".
    iMod (wp_step with "[HW He' Hsl]") as "H"; eauto; try iFrame.
    iModIntro; auto. iMod "H".
    iModIntro. iNext. iMod "H". iModIntro.
    iDestruct "H" as (c1') "(?&?&?&?)".
    iExists c1'. iFrame. 
Qed.

Lemma wptp_steps s n e1 t1 t2 σ1 σ2 c1 Φ :
  nsteps step n (e1 :: t1, σ1) (t2, σ2) →
  state_interp σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ∗ aux_interp c1 ⊢
  Nat.iter n (λ P, |={⊤, ∅}=> ▷ |={∅, ⊤}=> P) (∃ e2 t2' c1,
    ⌜t2 = e2 :: t2'⌝ ∗ state_interp σ2 ∗ WP e2 @ s; ⊤ {{ Φ }} ∗ wptp s t2' ∗ aux_interp c1).
Proof.
  revert e1 t1 t2 σ1 σ2 c1; simpl; induction n as [|n IH]=> e1 t1 t2 σ1 σ2 c1 /=.
  { inversion_clear 1; iIntros "(?&?&?&?)"; iExists e1, t1, c1; iFrame; auto with *. }
  iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
  iMod (wptp_step with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq.
  iMod "H"; iModIntro. iNext.
  iMod "H". iModIntro. 
  iDestruct "H" as (c2) "H".
    by iApply IH.
Qed.

Lemma bupd_iter_laterN_mono n P Q `{!Plain Q} :
  (P ⊢ Q) → Nat.iter n (λ P, |==> ▷ P)%I P ⊢ ▷^n Q.
Proof.
  intros HPQ. induction n as [|n IH]=> //=. by rewrite IH bupd_plain.
Qed.

Lemma bupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |==> ▷ P) Q ⊢ Nat.iter n (λ P, |==> ▷ P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  by rewrite bupd_frame_l {1}(later_intro R) -later_sep IH.
Qed.

Lemma wptp_result s n e1 t1 v2 t2 σ1 σ2 c1 φ :
  nsteps step n (e1 :: t1, σ1) (of_val v2 :: t2, σ2) →
  state_interp σ1 ∗ WP e1 @ s; ⊤ {{ v, ⌜φ v⌝ }} ∗ wptp s t1 ∗ aux_interp c1 ⊢
                          Nat.iter (S n) (λ P, |={⊤, ∅}▷=> P) (⌜φ v2⌝).
Proof.
  intros. rewrite wptp_steps //.
  rewrite [a in _ ⊢ a]Nat_iter_S_r.
  apply step_fupd_iter_mono.
  iDestruct 1 as (e2 t2' c2) "(% & _ & H & Ha)". simplify_eq.
  iMod (wp_value_inv with "H") as "H".
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
Qed.

Lemma wp_safe E e σ Φ c1 :
  state_interp σ -∗ WP e @ E {{ Φ }} -∗ aux_interp c1 -∗
         (|={⊤, ∅}▷=> ⌜is_Some (to_val e) ∨ reducible e σ⌝).
Proof.
  rewrite wp_unfold /wp_pre. iIntros "Hσ H Ha".
  destruct (to_val e) as [v|] eqn:?; [eauto 10|].
  { iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
    iModIntro. iNext. iModIntro. eauto with *. }
  iApply (step_fupd_mask_mono E _ _ ∅); auto.
  iMod ("H" with "[$Hσ $Ha]") as "(Hred&H)".
  iDestruct "Hred" as %(e2&σ2&efs&Hstep).
  iModIntro; iNext.
  iDestruct "H" as (c2) "H".
  specialize (response_inhabited _ _ c1 c2 _ _ _ Hstep) => c3.
  iMod ("H" $! e2 σ2 efs c3 with "[// ]") as "(?&?&Hs&?)". 
  iModIntro. iPureIntro. right. do 3 eexists; eauto. 
Qed.

Lemma wptp_safe n e1 e2 t1 t2 σ1 σ2 Φ c1 :
  nsteps step n (e1 :: t1, σ1) (t2, σ2) → e2 ∈ t2 →
  state_interp σ1 ∗ WP e1 {{ Φ }} ∗ wptp NotStuck t1 ∗ aux_interp c1 ⊢
  Nat.iter (S n) (λ P, |={⊤, ∅}▷=> P) ⌜is_Some (to_val e2) ∨ reducible e2 σ2⌝.
Proof.
  intros ? He2. rewrite wptp_steps //.
  rewrite [a in _ ⊢ a]Nat_iter_S_r.
  apply step_fupd_iter_mono.
  iDestruct 1 as (e2' t2' c2) "(% & Hw & H & Htp & Ha)". simplify_eq.
  apply elem_of_cons in He2 as [<-|?].
  - iMod (wp_safe with "Hw H Ha") as "$"; auto.
  - iMod (wp_safe with "Hw [Htp] Ha") as "$"; auto. by iApply (big_sepL_elem_of with "Htp").
Qed.

Lemma wptp_invariance s n e1 e2 t1 t2 σ1 σ2 c1 φ Φ :
  nsteps step n (e1 :: t1, σ1) (t2, σ2) →
  (state_interp σ2 ={⊤,∅}=∗ ⌜φ⌝) ∗ state_interp σ1 ∗ WP e1 @ s; ⊤ {{ Φ }} ∗ wptp s t1 ∗ aux_interp c1
  ⊢ Nat.iter (S n) (λ P, |={⊤, ∅}▷=> P) (|={⊤,∅}=> ⌜φ⌝).
Proof.
  intros ?. rewrite wptp_steps // step_fupd_iter_frame_l.
  rewrite [a in _ ⊢ a]Nat_iter_S_r.
  apply step_fupd_iter_mono.
  iIntros "[Hback H]".
  iDestruct "H" as (e2' t2' c2') "(% & Hσ & _)"; subst.
  iSpecialize ("Hback" with "Hσ").
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
Qed.
    
End adequacy.

Lemma fupd_soundness `{invPreG Σ} φ n :
  (∀ `{Hinv: invG Σ}, ▷^n |={⊤,∅}=> ⌜φ⌝)%I → φ.
  iIntros (Hwp). eapply (soundness (M:=iResUR Σ) _ (S n)). rewrite laterN_later.
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  rewrite fupd_eq in Hwp.
  iPoseProof (Hwp with "[$Hw $HE]") as "H". iNext.
  iMod "H" as ">(?&?&?)"; auto.
Qed.

Lemma step_fupd_soundness `{invPreG Σ} φ n :
      (∀ `{Hinv: invG Σ}, Nat.iter n (λ P, |={⊤, ∅}▷=> P) (|={⊤, ∅}=> ⌜ φ ⌝))%I  → φ.
Proof.
  iIntros (Hwp). eapply (soundness (M:=iResUR Σ) _  (S n)).
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  rewrite fupd_eq in Hwp. iPoseProof Hwp as "Hwp"; clear Hwp.
  iSpecialize ("Hwp" $! Hinv). iRevert "Hwp".
  rewrite persistently_elim. iIntros "Hwp".
  iInduction n as [|n] "IH".
  - rewrite //=. iMod ("Hwp" with "[$Hw $HE]") as ">(Hw&HE&H)".
    by iNext.
  - iMod ("Hwp" with "[$Hw $HE]") as ">(Hw&HE&H)".
    rewrite (later_laterN ((S n))). iNext.
    iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
    iApply ("IH" with "Hw HE [H]").
    rewrite //=.
Qed.

Lemma step_fupd_soundness'' `{invPreG Σ} P n :
  (∀ `{Hinv: invG Σ}, Nat.iter n (λ P, |={⊤, ∅}▷=> P) P)%I  →
  (Nat.iter (S n) (λ P, |==> ▷ P) P)%I.
Proof.
  iIntros (Hwp).
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  rewrite fupd_eq in Hwp. iPoseProof Hwp as "Hwp"; clear Hwp.
  iSpecialize ("Hwp" $! Hinv). iRevert "Hwp".
  rewrite persistently_elim. iIntros "Hwp".
  iInduction n as [|n] "IH".
  - rewrite //=.
  - iMod ("Hwp" with "[$Hw $HE]") as ">(Hw&HE&H)".
    iModIntro. iNext.
    iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
    iApply ("IH" with "Hw HE [H]") => //=.
Qed.
  
Lemma step_fupd_soundness' `{invPreG Σ} φ n :
      (∀ `{Hinv: invG Σ}, Nat.iter n (λ P, |={⊤, ∅}▷=> P) (⌜ φ ⌝))%I  → φ.
Proof.
  iIntros (Hiter). eapply (step_fupd_soundness _ n).
  iIntros (Hinv). iPoseProof (Hiter $! Hinv) as "Hiter".
  iApply (step_fupd_iter_mono with "Hiter").
  rewrite fupd_eq /fupd_def. iIntros (?) "(Hw&HE)".
  iMod (ownE_empty). by iFrame.
Qed.

Theorem wp_adequacy Σ Λ `{invPreG Σ} s e σ φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ (stateI : state Λ → iProp Σ) aTy auxI cTy rTy stepI Hpf1 Hpf2 c,
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI aTy auxI cTy rTy stepI Hpf1 Hpf2 in
       stateI σ ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }} ∗ aux_interp c)%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; split.
  - intros t2 σ2 v2 [n ?]%rtc_nsteps.
    eapply (step_fupd_soundness' _ (S (S n))).
    iIntros (Hinv).
    rewrite Nat_iter_S.
    iMod (Hwp Hinv) as (Istate aTy auxI cTy rTy stepI Hpf1 Hpf2) "H".
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto. iModIntro. iNext; iModIntro.
    iDestruct "H" as (c) "(HI&Hwp&Ha)".
    iApply (@wptp_result _ _ (IrisG _ _ Hinv Istate aTy auxI cTy rTy stepI Hpf1 Hpf2));
      eauto with iFrame.
  - destruct s; last done. intros t2 σ2 e2 _ [n ?]%rtc_nsteps ?.
    eapply (step_fupd_soundness' _ (S (S n))).
    iIntros (Hinv).
    rewrite Nat_iter_S.
    iMod (Hwp Hinv) as (Istate aTy auxI cTy rTy stepI Hpf1 Hpf2) "H".
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto. iModIntro. iNext; iModIntro.
    iDestruct "H" as (c) "(HI&Hwp&Ha)".
    iApply (@wptp_safe _ _ (IrisG _ _ Hinv Istate aTy auxI cTy rTy stepI Hpf1 Hpf2));
      eauto with iFrame.
Qed.

Theorem wp_invariance Σ Λ `{invPreG Σ} s e σ1 t2 σ2 φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ (stateI : state Λ → iProp Σ) aTy auxI cTy rTy stepI Hpf1 Hpf2 c,
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI aTy auxI cTy rTy stepI Hpf1 Hpf2 in
       stateI σ1 ∗ WP e @ s; ⊤ {{ _, True }} ∗ aux_interp c ∗ (stateI σ2 ={⊤,∅}=∗ ⌜φ⌝))%I) →
  rtc step ([e], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n ?]%rtc_nsteps.
  eapply (step_fupd_soundness _ (S (S n))).
  iIntros (Hinv). rewrite Nat_iter_S.
  iMod (Hwp Hinv) as (Istate aTy auxI cTy rTy stepI Hpf1 Hpf2) "H".
  iDestruct "H" as (c) "(HIstate & Hwp & Ha & Hclose)".
  iApply (@wptp_invariance _ _ (IrisG _ _ Hinv Istate aTy auxI cTy rTy stepI Hpf1 Hpf2));
    eauto.
  iApply (step_fupd_mask_mono ∅ _ _ ∅); auto.
  iModIntro; iNext; iModIntro.
  by iFrame.
Qed.
