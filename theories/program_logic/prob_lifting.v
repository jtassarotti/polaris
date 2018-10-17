Require Import Reals.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op soundness.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import prob_language lifting.
Set Default Proof Using "Type".
Import uPred.

From discprob.idxval Require Import pival pival_dist pidist_singleton idist_pidist_pair ival_dist irrel_equiv ival_pair.
From discprob.basic Require Import monad.

Definition prob_state := {X : Type & pidist X}.
Definition ps_eq : relation prob_state.
  intros (X1&Ix1) (X2&Ix2).
  exact ( ∃ (Hpf: X1 = X2), eq_pidist (eq_rect _ _ Ix1 _ Hpf) (Ix2)).
Defined.

Global Instance pidist_Equiv {X} : @Equiv (@pidist X) := eq_pidist.
Global Instance pidist_equiv {X} : @Equivalence (@pidist X) eq_pidist.
Proof.
  split.
  - intros ?; reflexivity. 
  - intros ???; by symmetry.
  - intros ????; etransitivity; eauto.
Qed.
  
Global Instance prob_state_Equiv : @Equiv prob_state := ps_eq.
Global Instance prob_state_equiv : @Equivalence prob_state ps_eq.
Proof.
  rewrite /ps_eq.
  split.
  - intros (X&Ix). exists (Logic.eq_refl) => //=.
  - intros (X&Ix) (Y&Iy) (HeqTy&Heqelt&HeqIs).
    exists (Logic.eq_sym HeqTy); split; destruct HeqTy => //=.
  - intros (X&Ix) (Y&Iy) (Z&Iz) (HeqTy1&Heqelt1&HeqIs1) (HeqTy2&Heqelt2&HeqIs2).
    destruct HeqTy1, HeqTy2; exists (Logic.eq_refl) => //=.
    rewrite //= in Heqelt1 Heqelt2 HeqIs1 HeqIs2.
    split; etransitivity; eauto.
Qed.

Class probG' (Σ : gFunctors) := ProbG {
  probG_invG : invG Σ;
  probG_name : gname;
  probG_inG :> inG Σ (authR (optionUR (exclR (discreteC prob_state))));
}.

Class stateG' (Λ: probLanguage) (Σ : gFunctors) := StateG {
  stateG_interp : (language.state Λ) → iProp Σ
}.

Notation probG Σ := (probG' Σ).

Definition ownProbRaw `{@probG' Σ} {X} (Is: pidist X) : iProp Σ :=
  own probG_name (◯ (Excl' (existT X Is : discreteC prob_state))).
Typeclasses Opaque ownProbRaw.
Instance: Params (@ownProbRaw) 9.
Global Instance ownProbRaw_timeless `{@probG' Σ} {X} (I: pidist X)  : Timeless (ownProbRaw I).
Proof. rewrite /ownProbRaw. apply _. Qed.

Definition ownProb `{@probG' Σ} {X} (Is: pidist X) : iProp Σ :=
  (∃ Is', ⌜ irrel_pidist Is Is' ⌝ ∗ ownProbRaw Is')%I.
Typeclasses Opaque ownProb.
Instance: Params (@ownProb) 9.
Global Instance ownProb_timeless `{@probG' Σ} {X} (I: pidist X)  : Timeless (ownProb I).
Proof. rewrite /ownProb. apply _. Qed.

Global Instance ownProbRaw_proper `{@probG' Σ} {X}:
  Proper ((≡) ==> (⊣⊢)) (@ownProbRaw _ _ X).
Proof.
  intros Is Is' Hequiv.
  rewrite /ownProbRaw.
  assert (existT X Is ≡ existT X Is') as Hequiv'.
  { rewrite /equiv/ps_eq//=. exists Logic.eq_refl => //=. }
  setoid_rewrite Hequiv'.
  done.
Qed.

Global Instance ownProb_proper `{@probG' Σ} {X}:
  Proper ((≡) ==> (⊣⊢)) (@ownProb _ _ X).
Proof.
  intros Is Is' Hequiv.
  rewrite /ownProb. setoid_rewrite Hequiv. done.
Qed.

Global Instance ownProb_anti `{@probG' Σ} {X}:
  Proper ((le_pidist) ==> flip (⊢)) (@ownProb _ _ X).
Proof.
  intros Is Is' Hequiv.
  rewrite /ownProb.
  assert (irrel_pidist Is Is') as Hequiv'.
  { 
    eapply irrel_pidist_proper; first eassumption.
    { reflexivity.  }
    { reflexivity.  }
  }
  setoid_rewrite Hequiv'. done.
Qed.

Global Instance ownProb_anti_irrel `{@probG' Σ} {X}:
  Proper ((irrel_pidist) ==> flip (⊢)) (@ownProb _ _ X).
Proof.
  intros Is Is' Hequiv.
  rewrite /ownProb.
  setoid_rewrite Hequiv. done.
Qed.

Lemma ownProb_anti_irrel' `{@probG' Σ} {X} (Is1 Is2: pidist X):
  irrel_pidist Is2 Is1 →
  ownProb Is1 ⊢ ownProb Is2.
Proof.
  intros. by apply ownProb_anti_irrel.
Qed.

Record ctype {Λ} `{@probG' Σ} e1 σ1 (c: prob_state) :=
  { choice_hd_type : Type;
     choice_hd_pidist : pidist choice_hd_type;
     choice_cont : choice_hd_type →  pidist (projT1 c);
     choice_equiv : irrel_pidist  (mbind (choice_cont) (choice_hd_pidist)) (projT2 c);
     choice_post : prim_step_result → choice_hd_type → Prop;
     choice_coupling :> irrel_couplingP (@ivdist_prim_step Λ e1 σ1) choice_hd_pidist choice_post}.

Arguments choice_cont {_ _ _ _ _ _} _ _ .

Lemma probG_irisG_response_inhabited1 `{@probG' Σ} Λ:
  ∀ (e1 : language.expr (prob_lang Λ)) (σ1 : language.state (prob_lang Λ)) 
  (c1 : prob_state) (c2 : ctype e1 σ1 c1) (e2 : language.expr (prob_lang Λ))
  (σ2 : language.state (prob_lang Λ)) (efs : list (language.expr (prob_lang Λ))),
  language.prim_step e1 σ1 e2 σ2 efs
  → rsupport (choice_coupling e1 σ1 c1 c2) (prim_res_step e2 σ2 efs).
Proof.
  intros e1 σ1 c1 c2 e2 σ2 efs Hprim. 
  destruct c1 as (X&x&Ix).
  destruct c2 as [Y m f Hequiv P [Istep' Is' Hirrel1 ? Ic]].
  specialize (ivdist_step_idx e1 _ _ _ _ Hprim); eauto.
  intros (istep&Hind&Hgt)%ClassicalEpsilon.constructive_indefinite_description.
  rewrite /response_type//=/rsupport//=.
  rewrite //=/rsupport.
  destruct Ic as [? ? Ic].
  destruct Ic as [Ic Hp1 Hp2].
  destruct (irrel_ivd_support_coerce _ _ Hirrel1 (prim_res_step e2 σ2 efs)) as (_&Hco2).
  eapply (ClassicalEpsilon.constructive_indefinite_description) in Hco2; last first.
  { rewrite //=. exists istep; split; auto. }
  edestruct Hco2 as (istep'&Hind'&Hgt').
  rewrite //=. 

  apply (ClassicalEpsilon.constructive_indefinite_description) in Hp1.
  destruct Hp1 as (h1&Hp1).
  unshelve eexists.
  { refine (snd (proj1_sig (ival.ind Ic _))).
    destruct (h1 (ival.coerce_supp _ _ Hgt')) as ((iic&?)&?).
    exact iic.
  }
  destruct Hp1 as (?&?&?&Hind_equiv&Hval_equiv).
  specialize (Hval_equiv (ival.coerce_supp _ _ Hgt')).
  specialize (Hind_equiv (ival.coerce_supp _ _ Hgt')).
  destruct (h1 _) as ((iic&?)&?) => //=.
  case_eq (ival.ind Ic iic). intros (?&?) ? Heq.
  rewrite //= Heq //= in Hind_equiv.
  exists iic; unshelve eexists.
  { 
  rewrite //= in Hind'. rewrite -Hind' -Hind_equiv //=. 
  }
  rewrite //= in Hind_equiv *; split.
  * clear -Heq. apply sval.sval_inj_pi => //=. rewrite Heq => //=. 
    f_equal. by rewrite Hind_equiv Hind'. 
  * rewrite //= in Hval_equiv.
    rewrite Rmult_1_r in Hval_equiv; auto.
    rewrite Hval_equiv. auto with *.
Qed.

Lemma probG_irisG_response_inhabited2 `{@probG' Σ} Λ:
  ∀ (e1 : language.expr (prob_lang Λ)) (σ1 : language.state (prob_lang Λ)) 
  (c1 : prob_state) (c2 : ctype e1 σ1 c1) (e2 : language.expr (prob_lang Λ))
  (σ2 : language.state (prob_lang Λ)) (efs : list (language.expr (prob_lang Λ))),
  language.prim_step e1 σ1 e2 σ2 efs
  → { x : choice_hd_type _ _ _ c2 | choice_post _ _ _ c2 (prim_res_step e2 σ2 efs) x}.   
Proof.
  intros.
  edestruct (probG_irisG_response_inhabited1 _ e1 σ1 c1 c2 e2 σ2 efs) as (x&Hpf); first eassumption.
  exists x. destruct Hpf as (i&Hpf&?); eauto.
Qed.

Instance probG_irisG  `{@probG' Σ} `{stateG' Λ Σ} : irisG' Λ Σ.
Proof.
refine {|
  iris_invG := probG_invG;
  state_interp σ := stateG_interp σ;
  aux_state := prob_state;
  aux_interp c := own probG_name (● (Excl' (c:discreteC prob_state)));
  choice_type := λ e1 σ1 c1, ctype e1 σ1 c1;
  response_type := λ e1 σ1 c1 c2 e2 σ2 efs, { x : choice_hd_type _ _ _ c2 | choice_post _ _ _ c2 (prim_res_step e2 σ2 efs) x};
  step_interpR := λ e1 σ1 c1 c2 e2 σ2 efs c3,
                  own probG_name (● (Excl' (existT (projT1 c1)
                                           (@choice_cont _ _ _ _ _ _ c2 (proj1_sig c3) : pidist (projT1 c1)) :
                                         discreteC prob_state)))
|}.
- abstract (iIntros (e1 σ1 c1 c2 e2 σ2 efs c3) "H";
  destruct c1 as (X&(x&Ix));
  destruct c2 as [Y m f Hequiv P Icoupling];
  destruct c3 as (y&Hgt);
  rewrite //=;
  iExists (existT X (f y) : discreteC prob_state);
  done).
- apply probG_irisG_response_inhabited2.
Defined.

Section lifting.
Context {Λ : probLanguage}.
Context `{stateG' Λ Σ} `{probG Σ}.
Hint Extern 2 (language.to_val _ = None) => apply (reducible_not_val _ inhabitant).

Lemma wp_pure_step_fupd `{Inhabited (state Λ)} s E E' e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros ([??] Hφ) "HWP".
  iApply (wp_lift_pure_det_step with "[HWP]"); [eauto|naive_solver|].
  { intros.  destruct s; auto. }
  iIntros (σ1 c1) "Ha". iMod "HWP". iModIntro. iNext.
  destruct c1 as (X&Ix).
  unshelve(
  iExists {| choice_hd_type := unit;
             choice_hd_pidist := mret tt;
             choice_cont := (λ x, _);
             choice_equiv := _;
             choice_post := λ x y, True;
             choice_coupling := irrel_coupling_trivial _ _|}).
  { exact Ix. } 
  { rewrite //=. setoid_rewrite pidist_left_id. reflexivity. }
  iMod "HWP". iModIntro. iIntros (c3).
  iFrame "HWP".
  rewrite //= /response_type//= in c3 *.
  iFrame.
Qed.

Lemma wp_pure_step_later `{Inhabited (state Λ)} s E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  ▷ WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  intros ??. rewrite -wp_pure_step_fupd //. rewrite -step_fupd_intro //.
Qed.

Lemma prob_update {X Y} (Is: pidist X) (Is': pidist Y) :
  ◯ Excl' (existT X Is : discreteC prob_state)
    ⋅ ● Excl' (existT X Is : discreteC prob_state) ~~>
    ◯ Excl' (existT Y Is' : discreteC prob_state)
    ⋅ ● Excl' (existT Y Is' : discreteC prob_state).
Proof.
  apply (auth_update (Excl' (existT X Is : discreteC prob_state))).
  apply option_local_update, exclusive_local_update.
  econstructor.
Qed.

Lemma wp_lift_step_couple {X Y} s E Φ e1 (Is: pidist X) (g: X → pidist Y) R:
  to_val e1 = None →
   ▷ ownProb (x ← Is; g x) ∗ (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
   ▷ ∃ (ic: irrel_couplingP (ivdist_prim_step e1 σ1) Is R), ∀ e2 σ2 efs (x: X),
      (⌜prim_step e1 σ1 e2 σ2 efs⌝ ∗ ⌜R (prim_res_step e2 σ2 efs) x⌝) ∗ ownProb (g x)  ={∅,E}=∗
      state_interp σ2 ∗
      WP e2 @ s; E {{ λ v, (Φ v) }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
           ⊢ WP e1 @ s; E {{ λ v, (Φ v) }}. 
Proof.
  iIntros (Htoval) "(Hown&Hwand)". iApply wp_lift_step; first done.
  iIntros (σ1 c1) "(Hσ&Ha)".
  iMod ("Hwand" $! σ1 with "Hσ") as "($&H)".
  iModIntro.
  rewrite /ownProb/ownProbRaw.
  iNext.
  iDestruct "Hown" as (Is'') "(%&Hprob)".
  iDestruct (own_valid_2 with "Ha Hprob") as %Hval.
  apply auth_valid_discrete_2 in Hval as (Hequiv%Excl_included&?).
  symmetry in Hequiv.
  setoid_rewrite <-Hequiv at 1.
  symmetry in Hequiv.
  iDestruct "H" as (ic) "H".
  destruct c1 as (X'&Is').
  rewrite /equiv/ofe_equiv/ps_eq//= in Hequiv.
  destruct Hequiv as (Heq&Heq_spidist).
  rewrite //= in Heq_spidist.
  unshelve (iExists _).
  { unshelve (refine ({| choice_hd_type := X;
             choice_hd_pidist := Is;
             choice_cont := _;
             choice_equiv := _;
             choice_post := _;
             choice_coupling := _ |})); try eapply Ic'.
    { subst. apply g. }
    { eapply R. }
    { abstract (rewrite //=; subst; rewrite /internal_eq_rew_r_dep//=; rewrite -Heq_spidist //=). }
    { apply ic. }
  }
  iIntros (e2' σ2' ef' c3).
  iIntros (Hstep).
  destruct c3 as (x&Hx).
  iSpecialize ("H" $! e2' σ2' ef' x).
  unshelve (iMod (own_update_2  with "Hprob Ha") as "[Hσ Hσf]").
  { exact ( ◯ Excl' (existT _ ((g x)) : discreteC prob_state)). }
  { exact ( ● Excl' (existT _ ((g x)) : discreteC prob_state)). }
  { eapply prob_update. }
  iMod ("H" with "[Hσf]") as "($&Hval&$)".
  { iSplitR.
    * abstract (iSplit; iPureIntro;  eauto; destruct Hx as (i&Hpf&Hval&?); eauto).
    * iExists _; iFrame. iPureIntro; auto; reflexivity.
  }
  iModIntro. iFrame.
  rewrite //=. clear Hx.
  rewrite /choice_hd_type in x *.
  iApply own.own_proper; last auto.
  apply Auth_proper; auto.
  apply Some_proper.
  apply Excl_proper; auto.
  apply Some_proper.
  apply Excl_proper; auto.
  symmetry. unshelve (esplit); eauto.
  subst => //=.
Qed.

Lemma wp_lift_step_nocouple s E Φ e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs,
      ⌜prim_step e1 σ1 e2 σ2 efs⌝  ={∅,E}=∗
      state_interp σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step s E _ e1)=>//; iIntros (σ1 c1) "(Hσ1&Ha)".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iModIntro; iNext.
  destruct c1 as (X&Ix).
  unshelve(
  iExists {| choice_hd_type := unit;
             choice_hd_pidist := mret tt;
             choice_cont := (λ x, _);
             choice_equiv := _;
             choice_post := λ x y, True;
             choice_coupling := irrel_coupling_trivial _ _|}).
  { exact Ix. } 
  { rewrite //=. setoid_rewrite pidist_left_id. reflexivity. }
  iIntros (e2 σ2 efs c3) "%".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  iModIntro. iSplitR "Ha"; auto.
Qed.

Lemma wp_lift_atomic_step_couple {X Y} s E Φ e1 (Is: pidist X) (g: X → pidist Y) R:
  to_val e1 = None →
   ▷ ownProb (x ← Is; g x) ∗ (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
   ▷ ∃ (ic: irrel_couplingP (ivdist_prim_step e1 σ1) Is R), ∀ e2 σ2 efs (x: X),
      (⌜prim_step e1 σ1 e2 σ2 efs⌝ ∗ ⌜R (prim_res_step e2 σ2 efs) x⌝) ∗ ownProb (g x) ={∅,E}=∗
      state_interp σ2 ∗
      (default False (to_val e2) Φ) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
           ⊢ WP e1 @ s; E {{ λ v, (Φ v) }}. 
Proof.
  iIntros (Htoval) "(Hown&Hwand)".
  iApply wp_lift_step_couple; auto.
  iFrame "Hown". iIntros (σ1) "Hσ".
  iMod ("Hwand" $! σ1 with "Hσ") as "($&H)".
  iModIntro.
  iNext. iDestruct "H" as (ic) "H". iExists ic. iIntros (e2 ???) "Hp".
  iMod ("H" with "Hp") as "(Hσ&Hphi&?)"; first eauto.
  iFrame. iModIntro.
  destruct (to_val e2) eqn:Heq_val; last auto.
  iApply wp_value; eauto.
Qed.

(*
Lemma wp_lift_atomic_step_couple' {X Y} s E Φ e1 (Is: pidist X) (g: X → pidist Y) R:
  to_val e1 = None →
   ▷ ownProb (x ← Is; g x) ∗ (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
   ▷ ∃ (ic: irrel_couplingP (ivdist_prim_step e1 σ1) Is R), ∀ e2 σ2 efs (x: X),
      (⌜prim_step e1 σ1 e2 σ2 efs⌝ ∗ ⌜R (prim_res_step e2 σ2 efs) x⌝)  ={∅,E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
           ⊢ WP e1 @ s; E {{ λ v, (Φ v) ∗ ∃ σ2 efs x, ⌜ R (prim_res_step (of_val v) σ2 efs) x ⌝
                                                         ∗ ownProb (g x)}}.
Proof.
  iIntros (Htoval) "(Hown&Hwand)".
  iApply wp_lift_step_couple; auto.
  iFrame "Hown". iIntros (σ1) "Hσ".
  iMod ("Hwand" $! σ1 with "Hσ") as "($&H)".
  iModIntro.
  iNext. iDestruct "H" as (ic) "H". iExists ic. iIntros (e2 ??? Hp).
  iMod ("H" with "[%]") as "(Hσ&?&?)"; first eauto.
  iFrame. iModIntro. iIntros "Hown".
  destruct (to_val e2) eqn:Heq_val; last auto.
  iApply wp_value; eauto.
  iFrame. iExists _, _, _; iFrame; iPureIntro.
  rewrite (of_to_val e2); auto. intuition eauto.
Qed.

Lemma wp_lift_atomic_step_couple_prop {X Y} s E Φ e1 (Is: pidist X) (g: X → pidist Y) R:
  to_val e1 = None →
   ▷ ownProb (x ← Is; g x) ∗ (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
   ▷ ⌜ irrel_coupling_propP (ivdist_prim_step e1 σ1) Is R ⌝ ∗ ∀ e2 σ2 efs (x: X),
      (⌜prim_step e1 σ1 e2 σ2 efs⌝ ∗ ⌜R (prim_res_step e2 σ2 efs) x⌝)  ={∅,E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
           ⊢ WP e1 @ s; E {{ λ v, (Φ v) ∗ ∃ σ2 efs x, ⌜ R (prim_res_step (of_val v) σ2 efs) x ⌝
                                                         ∗ ownProb (g x)}}.
Proof.
  iIntros (?) "(Hown&Hwand)". iApply wp_lift_atomic_step_couple; eauto.
  iFrame "Hown". iIntros. iMod ("Hwand" $! _ with "[$]") as "H".
  iModIntro. iDestruct "H" as "($&Hprop)".
  iNext. iDestruct "Hprop" as (Hp) "Hc".
  unshelve (iExists _).
  { apply ic_prop_to_wit; eauto. }
  auto.
Qed.
*)

Lemma wp_lift_pure_step_nocouple `{Inhabited (state Λ)} s E E' Φ e1 :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s ; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step s E); try done.
  { destruct s; auto. }
  iIntros (σ1 c1) "Ha". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first set_solver.
  iNext.
  destruct c1 as (X&Ix).
  unshelve(
  iExists {| choice_hd_type := unit;
             choice_hd_pidist := mret tt;
             choice_cont := (λ x, _);
             choice_equiv := _;
             choice_post := λ x y, True;
             choice_coupling := irrel_coupling_trivial _ _|}).
  { exact Ix. } 
  { rewrite //=. setoid_rewrite pidist_left_id. reflexivity. }
  iMod "H". iModIntro. iIntros (e2 efs c3) "Hstep".
  rewrite //=. iFrame; iApply "H". auto.
Qed.

Lemma wp_lift_atomic_step_nocouple {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply (wp_lift_step s E _ e1)=>//; iIntros (σ1 c1) "(Hσ1&Ha)".
  iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro; iNext.
  destruct c1 as (X&Ix).
  unshelve(
  iExists {| choice_hd_type := unit;
             choice_hd_pidist := mret tt;
             choice_cont := (λ x, _);
             choice_equiv := _;
             choice_post := λ x y, True;
             choice_coupling := irrel_coupling_trivial _ _|}).
  { exact Ix. } 
  { rewrite //=. setoid_rewrite pidist_left_id. reflexivity. }
  iIntros (e2 σ2 efs c3) "%". iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "($ & HΦ & $)"; first by eauto.
  destruct (to_val e2) eqn:?; last by iExFalso.
  iModIntro. iSplitR "Ha"; auto.
  by iApply wp_value.
Qed.

Lemma wp_lift_pure_det_step_nocouple `{Inhabited (state Λ)} {s E E' Φ} e1 e2 efs :
  (∀ σ1, reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs')→
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s ; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_nocouple s E); try done.
  { by intros; eapply Hpuredet. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  by iIntros (e' efs' σ (_&->&->)%Hpuredet).
Qed.


Lemma wp_prob_bind K `{!ProbLanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  apply: wp_bind.
  intros e1 σ1 c1 c2.
  destruct c1 as (X&x&Ix).
  destruct c2 as [Y m f Hequiv P Ic]. 
  unshelve (eexists).
  {
    refine {| choice_hd_type := Y;
              choice_hd_pidist := m;
              choice_cont := f;
              choice_equiv := Hequiv;
              choice_post := _;
              choice_coupling := _ |}.
    unshelve (apply ivdist_bind_coupling; eauto; destruct s; auto); last eapply Ic.
  }
  rewrite /response_type//=.
  intros e2 σ2 efs (y&e2'&Heq).
  rewrite //= in Heq *.
  destruct Heq as (Hpf&Hind&?).
  assert (e2 = e2').
  { apply: (@fill_inj _ K). auto. }
  subst.
  unshelve (eexists).
  { exists y. eapply Hpf. }
  auto.
Qed.


Lemma wp_prob_bind_inv K `{!ProbLanguageCtx K} s E e Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  apply: weakestpre.wp_bind_inv.
  intros e1 σ1 c1 c2.
  destruct c1 as (X&x&Ix).
  destruct c2 as [Y m f Hequiv P Ic]. 
  unshelve (eexists).
  {
    refine {| choice_hd_type := Y;
              choice_hd_pidist := m;
              choice_cont := f;
              choice_equiv := Hequiv;
              choice_post := _;
              choice_coupling := _ |}.
    unshelve (apply ivdist_bind_inv_coupling; eauto; destruct s; eauto); last eapply Ic.
  }
  rewrite /response_type//=.
  intros e2 σ2 efs (y&e2'&Heq).
  rewrite //= in Heq *.
  destruct Heq as (Hpf&Hind&?).
  unshelve (eexists).
  { exists y; eauto. }
  auto.
Qed.
  
End lifting.



From iris.program_logic Require Import ectx_language ectx_lifting.
Section ectx_lifting.
Context {Λ : ectxLanguage}.
Context  `{probG Σ} `{stateG' Λ Σ}.

Context {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Extern 2 (reducible ?e1 ?σ1) => apply head_prim_reducible.
Hint Extern 2 (head_step ?e1 ?σ1 ?e2 ?σ2 ?efs) => apply head_reducible_prim_step. 

Lemma wp_lift_atomic_head_step_couple {X Y} {s E Φ} e1 (Is: pidist X) (g: X → pidist Y) R:
  to_val e1 = None →
   ▷ ownProb (x ← Is; g x) ∗ (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
   ▷ ∃ (ic: irrel_couplingP (ivdist_prim_step e1 σ1) Is R), ∀ e2 σ2 efs (x: X),
      (⌜head_step e1 σ1 e2 σ2 efs⌝ ∗ ⌜R (prim_res_step e2 σ2 efs) x⌝) ∗ ownProb (g x) ={∅,E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
           ⊢ WP e1 @ s; E {{ λ v, (Φ v) }}. 
Proof using Hinh.
  iIntros (?) "(Hown&H)". iApply wp_lift_atomic_step_couple.
  { eauto. }
  iFrame "Hown".
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by destruct s; auto. iNext.
  iDestruct "H" as (c) "H".
  iExists c. iIntros (e2 σ2 efs c3) "(%&Hp)". iApply "H"; auto.
  iFrame.
  iSplit; iPureIntro; intuition; eauto.
Qed.

Lemma wp_lift_pure_head_step_nocouple {s E E' Φ} e1 :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → σ1 = σ2) →
  (|={E,E'}▷=> ∀ e2 efs σ, ⌜head_step e1 σ e2 σ efs⌝ →
    WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  iIntros (??) "H". iApply wp_lift_pure_step_nocouple; eauto.
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (????). iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_nocouple {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      state_interp σ2 ∗
      default False (to_val e2) Φ ∗ [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_nocouple; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by (destruct s; eauto). iNext. iIntros (e2 σ2 efs) "%". iApply "H"; auto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork_nocouple {s E Φ} e1 :
  to_val e1 = None →
  (∀ σ1, state_interp σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ⌜efs = []⌝ ∗ state_interp σ2 ∗ default False (to_val e2) Φ)
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step_nocouple; eauto.
  iIntros (σ1) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs) "%".
  iMod ("H" $! v2 σ2 efs with "[# //]") as "(% & $ & $)"; subst; auto.
Qed.

Lemma wp_lift_pure_det_head_step_nocouple {s E E' Φ} e1 e2 efs :
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ1 = σ2 ∧ e2 = e2' ∧ efs = efs') →
  (|={E,E'}▷=> WP e2 @ s; E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP ef @ s ; ⊤ {{ _, True }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh. eauto using wp_lift_pure_det_step_nocouple. Qed.

Lemma wp_prob_ectx_bind {s E e} K Φ :
  WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
Proof. apply: wp_prob_bind. Qed.

Lemma wp_prob_ectx_bind_inv {s E Φ} K e :
  WP fill K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }}.
Proof. apply: wp_prob_bind_inv. Qed.

End ectx_lifting.