Require Import Reals.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op soundness.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import prob_language prob_lifting.
Set Default Proof Using "Type".
Import uPred.

From discprob.idxval Require Import pival pival_dist pidist_singleton idist_pidist_pair ival_dist irrel_equiv ival_pair.
From discprob.basic Require Import monad.


Section adequacy.
Context {Λ : probLanguage}.
Context `{stateG' Λ Σ} `{probG Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation world σ := (state_interp σ)%I.

Notation wptp t := ([∗ list] ef ∈ t, WP ef {{ _, True }})%I.

Lemma wp_step' e1 σ1 c1 Φ:
  language.to_val e1 = None →
  world σ1 ∗ WP e1 {{ Φ }} ∗ aux_interp c1 ={⊤, ∅}=∗
        ▷ (⌜reducible e1 σ1⌝ ∧ ∃ c2, ∀ e2 σ2 efs c3,
        ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅, ⊤}=∗ (world σ2 ∗ WP e2 {{ Φ }} ∗ wptp efs
                                   ∗ step_interpR e1 σ1 c1 c2 e2 σ2 efs c3)).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (Hnone). iIntros "[Hσ [H Ha]]".
  rewrite Hnone.
  iMod ("H" $! σ1 c1 with "[$Hσ $Ha]") as "($ & H)".
  iModIntro; iNext.
  iDestruct "H" as (c) "H".
  iExists c. iIntros (e2 σ2 efs c3) "%".
  iMod ("H" $! e2 σ2 efs c3 with "[//]") as "($&$&$&$)"; auto.
Qed.

Lemma wp_step e1 σ1 c1 Φ:
  language.to_val e1 = None →
  world σ1 ∗ WP e1 {{ Φ }} ∗ aux_interp c1 ={⊤, ∅}=∗
        ▷ ∃ c2, ∀ e2 σ2 efs c3,
        ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅, ⊤}=∗ (world σ2 ∗ WP e2 {{ Φ }} ∗ wptp efs
                                   ∗ step_interpR e1 σ1 c1 c2 e2 σ2 efs c3).
Proof.
  iIntros (Hred) "H".
  iPoseProof (wp_step' with "H") as "H"; auto.
  iMod "H". iModIntro. iNext. 
  iDestruct "H" as "(_ & $)".
Qed.

Lemma wptp_step_hd e1 t σ1 c1 Φ :
  language.to_val e1 = None →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp t ∗ aux_interp c1  ={⊤, ∅}=∗
        ▷ (⌜ reducible e1 σ1⌝ ∧ ∃ c2, ∀ e2 σ2 efs c3,
        ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅, ⊤}=∗ (world σ2 ∗ WP e2 {{ Φ }} ∗ wptp (t ++ efs)
                                   ∗ step_interpR e1 σ1 c1 c2 e2 σ2 efs c3)).
Proof.
  iIntros (Hred) "(HW&He&Ht&Ha)".
  iPoseProof (wp_step' with "[HW He Ha]") as "H"; [ eauto | eauto |].
  { iFrame. }
  iMod "H". iModIntro. iNext.
  iDestruct "H" as "(% & H)".
  iSplit; auto.
  iDestruct "H" as (c) "H".
  iExists c. iIntros (e2 σ2 efs c3) "Hprim".
  iFrame. iSpecialize ("H" $! e2 σ2 efs c3 with "Hprim"); auto.
Qed.

Lemma rcons_app_single {A} (a: A) l : seq.rcons l a = seq.cat l (a :: nil).
Proof.
  induction l => //=; by f_equal.
Qed.

Opaque step_interpR.

Lemma wptp_step_tl e1 tl ei tr σ1 c1 Φ :
  language.to_val ei = None →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp (tl ++ ei :: tr) ∗ aux_interp c1
        ={⊤, ∅}=∗ ▷ (⌜ reducible ei σ1 ⌝ ∧  ∃ (c2: choice_type ei σ1 c1), ∀ ei' σ2 efs c3,
        ⌜prim_step ei σ1 ei' σ2 efs⌝
        ={∅, ⊤}=∗ (world σ2 ∗ WP e1 {{ Φ }} ∗ wptp (tl ++ ei' :: tr ++ efs) ∗ step_interpR ei σ1 c1 c2 ei' σ2 efs c3))%I.
Proof.
  iIntros (Hred).
  iIntros  "(HW & He & ($ & Hei& $) & Hsl)". iFrame "He".
  iFrame.
  iPoseProof (wp_step' with "[HW Hei Hsl]") as "Hstep"; [ done | iFrame | ].
  iMod "Hstep"; iModIntro. iNext. 
  iDestruct "Hstep" as (Hred' c2) "Hstep".
  iSplit; auto.
  iExists c2. iIntros (e2 σ2 efs c3) "Hprim".
  iMod ("Hstep" $! e2 σ2 efs c3 with "Hprim") as "($&$&$&$)"; auto. 
Qed.

Local Open Scope nat_scope.

Transparent step_interpR.

Lemma suffix_anti_symm {A} (l1 l2: list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l1 → l1 = l2.
Proof.
  destruct 1 as (ll1&Heq1).
  destruct 1 as (ll2&Heq2).
  rewrite Heq1 in Heq2.
  apply (f_equal length) in Heq2.
  rewrite ?app_length in Heq2.
  destruct ll1, ll2; rewrite //= in Heq2; try omega; try auto.
Qed.

Definition coupling_post {X} (φ : val Λ → X → Prop) (x : language.cfg Λ) y :=
  match x with
  | (e :: t, σ) =>
    match to_val e with
    | None => False
    | Some v => φ v y
    end
  | _ => False
  end.

Require Import Logic.Eqdep_dec.

Lemma cat_app {A} (l1 l2: list A):
  seq.cat l1 l2 = app l1 l2.
Proof. rewrite //=. Qed.

Lemma ic_bind_iProp {A1 A2 A1' A2'} (P: A1 → A2 → Prop) f1 f2 I1 Is2 Is0
      (Q : A1' → A2' → Prop) (Ic: irrel_couplingP I1 Is2 P):
  irrel_pidist (Is2 ≫= f2) Is0 →
  ((∀ xyS: { xy: A1 * A2 | P (fst xy) (snd xy )},
              (⌜ irrel_coupling_propP (f1 (fst (proj1_sig xyS)))
                                      (f2 (snd (proj1_sig xyS))) Q ⌝ : iProp Σ))%I
   ⊢ (⌜ irrel_coupling_propP (I1 ≫= f1) Is0 Q ⌝)%I).
Proof.
  intros Hle.
  iIntros (Hall).
  iPureIntro. eapply irrel_coupling_prop_irrel_Proper; first done.
  * eauto.
  * done.
  * eapply irrel_coupling_prop_bind; eauto.
    ** eexists; eauto.
    ** intros x y HP. eapply (Hall (exist _ (x, y) HP)). 
Qed.


Theorem wp_coupling {X: Type} n e t σ φ (Is0: pidist X)
        (sch : scheduler) (tr: trace)
        (Hterm: terminates sch (tr ++ ((e :: t, σ) :: nil)) n) :
  (world σ ∗ WP e {{ v, ∃ (v' : X), ownProb (mret v') ∗ ⌜φ v v'⌝ }}
         ∗ wptp t
         ∗ aux_interp (existT X Is0))%I ⊢
 Nat.iter (S n) (λ P, |={⊤, ∅}▷=> P)
          ⌜ irrel_coupling_propP (ivdist_trace_stepN_aux sch tr (e :: t) σ n) Is0 (coupling_post φ) ⌝.
Proof.
  iStartProof.
  iRevert (e t σ φ sch tr Is0 Hterm).
  iInduction n as [|n] "IH";
  iIntros (e t σ φ sch tr Is0 Hterm) "H".
  - iAssert ( |={⊤, ∅}▷=> ⌜∃ v v', e = of_val v ∧ irrel_pidist (mret v') Is0
                      ∧ coupling_post φ (of_val v :: t, σ) v'⌝)%I with "[H]"
      as "H"; last first.
    { rewrite //=.
      iMod "H"; iModIntro; iNext. iMod "H"; iModIntro.
      iDestruct "H" as %(v&v'&Heq1&Hle&Hpost); last first.
      iPureIntro. unshelve (eexists); last done.
      eapply irrel_coupling_mono_irrel.
      * reflexivity. 
      * eassumption.
      * subst. rewrite //=.
        eapply irrel_coupling_mret; eauto.
    }
    edestruct (Hterm tr (e :: t, σ) 0) as (v&tp'&Heqval); eauto.
    { econstructor. }
    inversion Heqval; subst.
    iExists v.
    iDestruct "H" as "(HW&He&Hwptp&Haux)".
    iAssert (|={⊤, ∅}▷=> ∃ (v' : X), ⌜irrel_pidist (mret v') Is0 ∧ φ v v'⌝)%I with
        "[HW He Hwptp Haux]" as "H"; last first.
    {
      iMod "H"; iModIntro; iNext; iMod "H"; iModIntro.
      iDestruct "H" as (v') "Hp". iDestruct "Hp" as %(Hle&Hφ).
      iPureIntro. exists v'; split_and!; auto.
      rewrite //= to_of_val //=.
    }
    iDestruct (wp_value_inv with "He") as "H".
    rewrite /ownProb.
    iMod "H" as (v') "(H&Hphi)".
    iDestruct "H" as (Is') "(Hle&Hown)".
      iApply (step_fupd_mask_mono ∅ _ _ ∅); [ auto | auto | ].
    iModIntro; iNext; iModIntro.
    rewrite /ownProbRaw.
      iDestruct (own_valid_2 with "Haux Hown")
          as %[(HeqTy&Heq_spi)%Excl_included _]%auth_valid_discrete_2; auto.
      iClear "Haux". iClear "Hown". 
      iDestruct "Hphi" as %Hphi.
      iDestruct "Hle" as %Hle.
      iPureIntro. clear -Hphi Heq_spi Hle.
      rewrite //= in Heq_spi.
      exists v' => //=; split; auto.
      etransitivity; first eassumption.
      rewrite -Heq_spi.
      rewrite -eq_rect_eq_dec; eauto; first reflexivity.
      intros. apply ClassicalEpsilon.excluded_middle_informative.
  - rewrite /ivdist_trace_stepN_aux.
    rewrite -/ivdist_trace_stepN_aux.
    rewrite /ivdist_trace_step.
    specialize (terminates_S sch tr (e :: t, σ)) => Hterm_Some.
    remember (sch (tr ++ [(e :: t, σ)])) as i eqn:Heq_sched.
    destruct ((e :: t) !! i) as [ei|] eqn:Hlookup; last first.
    { rewrite /ivdist_tpool_stepi. rewrite -Heq_sched Hlookup.
      setoid_rewrite ivd_left_id.
      setoid_rewrite ivd_left_id.
      rewrite Nat_iter_S.
      iApply (step_fupd_mask_mono ∅ _ _ ∅); [ done | done |].
      iModIntro. iNext. iModIntro.
      iApply "IH".
      iPureIntro.
      { subst. rewrite -cat_app. rewrite -seq.catA.
        eapply terminates_stutter_None; eauto. }
      eauto.
    }
    destruct (to_val ei) as [v|] eqn:Heq_val.
    { rewrite /ivdist_tpool_stepi. rewrite -Heq_sched Hlookup.
      setoid_rewrite ivdist_prim_step_val_mret; last first.
      { rewrite //=. congruence. }
      setoid_rewrite ivd_left_id.
      setoid_rewrite ivd_left_id.
      setoid_rewrite ivd_left_id.
      rewrite Nat_iter_S.
      iApply (step_fupd_mask_mono ∅ _ _ ∅); [ done | done |].
      iModIntro. iNext. iModIntro.
      iApply "IH".
      iPureIntro.
      { subst. rewrite -cat_app. rewrite -seq.catA.
        eapply terminates_stutter_value; eauto. congruence. }
      eauto.
    }
    symmetry in Heq_sched.
    destruct i as [|i].
    * rewrite Heq_sched.
      inversion Hlookup; subst.
      iPoseProof (wptp_step_hd ei t with "[H]") as "Hstep"; eauto.
      rewrite Nat_iter_S.
      iMod "Hstep"; iModIntro; iNext.
      iDestruct "Hstep" as (Hred C) "Hstep".
      destruct C as [Y m f Hequiv P Ic]. 
      iApply step_fupd_iter_mono.
      { setoid_rewrite ivd_assoc.
        setoid_rewrite ivd_assoc.
        rewrite /projT1/projT2 in f Hequiv *.
        simpl response_type.
        
        
        rewrite -(ic_bind_iProp _ _ _ (ivdist_prim_step ei σ) _ Is0 (coupling_post φ) _); swap 1 3.
        { eapply Hequiv. }
        { eapply (irrel_coupling_support _ _ _ Ic). } 
        iIntros "H". iApply "H".
      }
      erewrite (@step_fupd_iter_forall_pure_mid _ _); last first.
      { destruct (irrel_coupling_support_wit _ _ _ Ic) as ((x&y)&Hpf).
        unshelve exists. eexists (x, y). rewrite //=.
      }
      iIntros (xyS).
      destruct xyS as ((ei'&y)&HP).
      destruct ei' as [ei' σ' efs|]; last first. 
      { exfalso. destruct HP as (HP&Hsupp1&?). eapply ival_red_non_stuck; eauto. }
      
      setoid_rewrite ivd_left_id. 
      setoid_rewrite ivd_left_id. 
      assert (prim_step ei σ ei' σ' efs).
      { destruct HP as (HP&Hsupp1&?); by apply ivdist_non_stuck_red; eauto. }
      assert ((∃ i Hpf, ival.ind Ic i = (exist _ (prim_res_step ei' σ' efs, y) Hpf)
                        ∧ ival.val Ic i > 0)%R) as Hsupp.
      { destruct HP as (HP&Hsupp1&?&(i0&?&?)).
        exists i0, HP; repeat split; auto. }
      iSpecialize ("Hstep" $! ei' σ' efs).
      unshelve (iSpecialize ("Hstep" $! _)).
      { eexists; eauto => //=. destruct HP; eauto. }
      iSpecialize ("Hstep" with "[% //]"). iMod "Hstep".
      iSpecialize ("IH" $! _ _ _ _ _ _ with "[%] Hstep"); last iFrame; auto.
      { rewrite //=. rewrite -app_assoc. eapply Hterm_Some; eauto.
        eapply (istep_atomic _ _ _ ei σ ei' σ' efs []); eauto; try f_equal. }
    * rewrite /ivdist_tpool_stepi.
      specialize (take_drop_middle _ _ _ Hlookup) => Hlook.
      rewrite Heq_sched. rewrite Hlookup.
      simpl in Hlookup.
      rewrite -(take_drop_middle _ _ _ Hlookup).

      iPoseProof (wptp_step_tl e _ ei with "[H]") as "Hstep"; eauto.
      rewrite Nat_iter_S.
      iMod "Hstep"; iModIntro; iNext.
      iDestruct "Hstep" as (Hred C) "Hstep".
      destruct C as [Y m f Hequiv P Ic]. 
      iApply step_fupd_iter_mono.
      { setoid_rewrite ivd_assoc.
        setoid_rewrite ivd_assoc.
        rewrite /projT1/projT2 in f Hequiv *.
        simpl response_type.
        
        
        rewrite -(ic_bind_iProp _ _ _ (ivdist_prim_step ei σ) _ Is0 (coupling_post φ) _); swap 1 3.
        { eapply Hequiv. }
        { eapply (irrel_coupling_support _ _ _ Ic). } 
        iIntros "H". iApply "H".
      }
      erewrite (@step_fupd_iter_forall_pure_mid _ _); last first.
      { destruct (irrel_coupling_support_wit _ _ _ Ic) as ((x&y)&Hpf).
        unshelve exists. eexists (x, y). rewrite //=.
      }
      iIntros (xyS).
      destruct xyS as ((ei'&y)&HP).
      destruct ei' as [ei' σ' efs|]; last first. 
      { exfalso. destruct HP as (HP&Hsupp1&?). eapply ival_red_non_stuck; eauto. }

      setoid_rewrite ivd_left_id. 
      setoid_rewrite ivd_left_id. 
      assert (prim_step ei σ ei' σ' efs).
      { destruct HP as (HP&Hsupp1&?); by apply ivdist_non_stuck_red; eauto. }
      assert ((∃ i Hpf, ival.ind Ic i = (exist _ (prim_res_step ei' σ' efs, y) Hpf)
                        ∧ ival.val Ic i > 0)%R) as Hsupp.
      { destruct HP as (HP&Hsupp1&?&(i0&?&?)).
        exists i0, HP; repeat split; auto. }
      iSpecialize ("Hstep" $! ei' σ' efs).
      rewrite /rsupport.
      rewrite //= in Hsupp.
      unshelve (iSpecialize ("Hstep" $! _)).
      { eexists; eauto. destruct HP; eauto. }
      iSpecialize ("Hstep" with "[% //]"). iMod "Hstep".
      repeat iMod "Hstep".
      assert (terminates sch ((tr ++ ((e :: t, σ) :: nil))
                                ++ (((seq.cat (take (S i) (e :: t))
                                              (seq.cat (ei' :: drop (S (S i)) (e :: t)) efs), σ'))
                                      :: nil)) n)
        as Hterm'.
      { rewrite //=. rewrite -app_assoc. eapply Hterm_Some; eauto.
        eapply (istep_atomic _ _ _ ei σ ei' σ' efs (take (S i) (e :: t))); eauto; try f_equal.
        - by rewrite take_drop_middle. 
        - rewrite take_length_le //.
          specialize (lookup_lt_Some _ _ _ Hlookup) => //=; omega.
      }
      clear Hterm.
      iSpecialize ("IH" $! _ _ _ _ _ _ _ with "[%] Hstep"); last iFrame; auto.
      { eauto. }
      iModIntro. rewrite //= in Hlook. rewrite Hlook //=.
Qed.

End adequacy.


Class probPreG (Λ: probLanguage) Σ := ProbPreG{
  pre_probG_inG :> inG Σ (authR (optionUR (exclR (discreteC prob_state))));
}.

From iris.program_logic Require Import adequacy.
Theorem wp_prob_adequacy {Y} `{invPreG Σ} `{@probPreG Λ Σ}
        e σ φ  Is sch n:
  (∀`{Hinv: invG Σ} (* `{Hprob : probG ex va st Λ Σ} *),
      (|={⊤}=> ∃ (stateI: _ → iProp Σ) pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ aux_interp (existT Y Is : prob_state) ∗
             WP e {{ v, ∃ v' : Y, ownProb (mret v') ∗ ⌜φ v v'⌝ }})%I) →
  terminates sch (((e :: nil), σ) :: nil) n →
  irrel_couplingP (ivdist_tpool_stepN sch (e :: nil) σ n)
                  Is
                  (coupling_post φ).
 Proof.
   intros Hwp Hterm. 
   apply ic_prop_to_wit.
   eapply (step_fupd_soundness' _ (S (S n))).
   iIntros (Hinv).
   rewrite Nat_iter_S.
   iMod (Hwp Hinv) as "Hwp".
   iDestruct "Hwp" as (Istate γ) "H".
   iDestruct "H" as "(HIstate & Ha & Hwp)".
   iApply (step_fupd_mask_mono ∅ _ _ ∅); auto. iModIntro. iNext; iModIntro.
   rewrite /ivdist_tpool_stepN.
   efeed pose proof (@wp_coupling Λ) as Hcoup; eauto; last first.
   iPoseProof (Hcoup with "[HIstate Ha Hwp]") as "H".
   { iFrame.  rewrite //=. }
   { eauto. }
   { eauto. }
Qed.

Definition coerce_cfg {Λ : probLanguage} (f: language.val Λ → R) (r: R) (ρ: cfg Λ) : R :=
  match fst ρ with
  | [] => r
  | e :: _ => match to_val e with
              | Some v => f v 
              | _ => r
              end
  end.

Theorem wp_prob_adequacy' {Y} `{invPreG Σ} `{@probPreG Λ Σ}
        e σ φ  Is sch n:
  (∀`{Hinv: invG Σ},
      (|={⊤}=> ∃ (stateI: _ → iProp Σ), ∀ pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ (ownProb Is -∗
             WP e {{ v, ∃ (v' : Y), ownProb (mret v') ∗ ⌜φ v v'⌝ }}))%I) →
  terminates sch (((e :: nil), σ) :: nil) n →
  irrel_couplingP (ivdist_tpool_stepN sch (e :: nil) σ n)
                  Is
                  (coupling_post φ).
 Proof.
   intros Hwp Hterm. 
   apply ic_prop_to_wit.
   eapply (step_fupd_soundness' _ (S (S n))).
   iIntros (Hinv).
   rewrite Nat_iter_S.
  iMod (own_alloc (● (Excl' (existT _ Is : discreteC prob_state)) ⋅
                   ◯ (Excl' (existT _ Is : discreteC prob_state))))
    as (γprob) "[Hσ Hσf]"; first done.
   iMod (Hwp Hinv) as "Hwp".
   iDestruct "Hwp" as (Istate) "H".
   iSpecialize ("H" $! γprob).
   iDestruct "H" as "(HIstate & HaHwp)".
   iApply (step_fupd_mask_mono ∅ _ _ ∅); auto. iModIntro. iNext; iModIntro.
   rewrite /ivdist_tpool_stepN.
   set (Hprob := ProbG Σ _ γprob _).
   efeed pose proof (@wp_coupling Λ _ {| stateG_interp := Istate |} Hprob) as Hcoup; eauto;
     last first.
   iPoseProof (Hcoup with "[HIstate HaHwp Hσf Hσ]") as "H".
   { rewrite /ownProb/ownProbRaw//=. iFrame.
     iSplitR "".
     * iApply ("HaHwp" with "[Hσf]").
       { iExists _; auto. }
     * rewrite //=.
   }
   { eauto. }
   { eauto. }
Qed.

Import Rbar.
From discprob.idxval Require Import extrema.

Theorem wp_prob_adequacy_Ex_max {Y} `{invPreG Σ} `{@probPreG Λ Σ}
        e σ φ (Is: pidist Y) sch f g d n:
  (∀`{Hinv: invG Σ},
      (|={⊤}=> ∃ (stateI: _ → iProp Σ), ∀ pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ (ownProb Is -∗
             WP e {{ v, ∃ (v' : Y), ownProb (mret v') ∗ ⌜φ v v'⌝ }}))%I) →
  (∀ v v', φ v v' → f v = g v') →
  terminates sch (((e :: nil), σ) :: nil) n →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (extrema.Ex_ival (coerce_cfg f d) (ivdist_tpool_stepN sch [e] σ n))
          (extrema.Ex_max g Is).
Proof.
  rewrite /coerce_cfg.
  intros. apply irrel_coupling_eq_Ex_max_supp; eauto.
  eapply irrel_coupling_conseq; last eapply wp_prob_adequacy'; eauto.
  { intros x y. rewrite /coupling_post.
    destruct x as (l&?). destruct l => //=.
    destruct to_val => //=. eauto. }
Qed.

Theorem wp_prob_adequacy_Ex_min {Y} `{invPreG Σ} `{@probPreG Λ Σ}
        e σ φ (Is: pidist Y) sch f g d n:
  (∀`{Hinv: invG Σ},
      (|={⊤}=> ∃ (stateI: _ → iProp Σ), ∀ pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ (ownProb Is -∗
             WP e {{ v, ∃ (v' : Y), ownProb (mret v') ∗ ⌜φ v v'⌝ }}))%I) →
  (∀ v v', φ v v' → f v = g v') →
  terminates sch (((e :: nil), σ) :: nil) n →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (extrema.Ex_min g Is)
          (extrema.Ex_ival (coerce_cfg f d) (ivdist_tpool_stepN sch [e] σ n)).
Proof.
  rewrite /coerce_cfg.
  intros. apply irrel_coupling_eq_Ex_min_supp; eauto.
  eapply irrel_coupling_conseq; last eapply wp_prob_adequacy'; eauto.
  { intros x y. rewrite /coupling_post.
    destruct x as (l&?). destruct l => //=.
    destruct to_val => //=. eauto. }
 Qed.

Theorem wp_prob_adequacy_ex_Ex {Y} `{invPreG Σ} `{@probPreG Λ Σ}
        e σ φ (Is: pidist Y) sch f g d n:
  (∀`{Hinv: invG Σ},
      (|={⊤}=> ∃ (stateI: _ → iProp Σ), ∀ pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ (ownProb Is -∗
             WP e {{ v, ∃ (v' : Y), ownProb (mret v') ∗ ⌜φ v v'⌝ }}))%I) →
  (∀ v v', φ v v' → f v = g v') →
  terminates sch (((e :: nil), σ) :: nil) n →
  bounded_fun_on g (λ x, In_psupport x Is) →
  ex_Ex_ival (coerce_cfg f d) (ivdist_tpool_stepN sch [e] σ n).
Proof.
  rewrite /coerce_cfg.
  intros. eapply irrel_coupling_eq_ex_Ex_supp; eauto.
  eapply irrel_coupling_conseq; last eapply wp_prob_adequacy'; eauto.
  { intros x y. rewrite /coupling_post.
    destruct x as (l&?). destruct l => //=.
    destruct to_val => //=. eauto. }
 Qed.

Theorem wp_prob_safety_adequacy Σ Λ `{invPreG Σ} `{@probPreG Λ Σ} {X} (Is: pidist X) s e σ φ :
  (∀ `{Hinv : invG Σ},
     (|={⊤}=> ∃ (stateI : state Λ → iProp Σ), ∀ pname,
      let _ : probG' Σ := ProbG Σ Hinv pname _ in
      let _ : stateG' Λ Σ := StateG Λ Σ stateI in
      stateI σ ∗ (ownProb Is -∗
                          WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}))%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (?) "".
  iMod (own_alloc (● (Excl' (existT _ Is : discreteC prob_state)) ⋅
                   ◯ (Excl' (existT _ Is : discreteC prob_state))))
    as (γprob) "[Hσ Hσf]"; first done.
  iMod Hwp as (stateI) "Hwp".
  iModIntro. iExists stateI. 
  set (Hprob := ProbG Σ Hinv γprob _).
  set (irisG' := @probG_irisG _ Hprob _ {| stateG_interp := stateI |}).
  iExists aux_state, aux_interp, choice_type, response_type, step_interpR.
  iExists step_to_aux, response_inhabited.
  iExists (existT _ Is : prob_state).
  iDestruct ("Hwp" $! γprob) as "($&Hwp)". iFrame.
  iSpecialize ("Hwp" with "[Hσf]").
  { rewrite /ownProb/ownProbRaw; iExists _; iFrame. auto. }
  auto.
Qed.