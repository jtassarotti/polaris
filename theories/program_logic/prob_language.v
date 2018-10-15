Require Import Reals Psatz.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language.
From discprob.basic Require Import base sval order monad bigop_ext nify.
  From discprob.idxval Require Import idist_pidist_pair pival_dist ival pival ival_dist pival_dist ival_pair pidist_singleton irrel_equiv idist_pidist_pair.
From discprob.monad Require Import monad.
From mathcomp Require Import ssreflect bigop seq choice fintype finset ssrbool eqtype.
Set Default Proof Using "Type".
From discprob.prob Require Import prob countable.

Section prob_language_mixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → expr → state → list expr → Prop).
  Context (prim_step_prob : expr → state → expr → state → list expr → R).

  Record ProbLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None;
    mixin_prim_step_count e σ: 
      Countable.class_of { esf: expr * state * list expr |
                           prim_step e σ (esf.1.1) (esf.1.2) (esf.2) };
    mixin_prim_step_sum1 e σ:
        (∃ e' σ' efs, prim_step e σ e' σ' efs) →
        is_series (countable_sum (λ t : Countable.Pack (mixin_prim_step_count e σ)
                                        { esf: expr * state * list expr |
                                          prim_step e σ (esf.1.1) (esf.1.2) (esf.2) },
                                    prim_step_prob e σ
                                                   (fst (fst (sval t)))
                                                   (snd (fst (sval t)))
                                                   (snd (sval t)))) 1;
    mixin_prim_step_nonneg : ∀ e1 σ1 e2 σ2 efs, (prim_step_prob e1 σ1 e2 σ2 efs >= 0)%R;
    mixin_prim_step_strict_gt :
    ∀ e1 σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs ↔ (prim_step_prob e1 σ1 e2 σ2 efs > 0)%R
  }.
End prob_language_mixin.

Structure probLanguage := ProbLanguage  {
  expr : Type;
  val : Type;
  state : Type;

  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → expr → state → list expr → Prop;

  prim_step_prob : expr → state → expr → state → list expr → R;

  prob_language_mixin :
    ProbLanguageMixin of_val to_val prim_step prim_step_prob;
}.

Arguments ProbLanguage {_ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments prim_step {_} _ _ _ _ _.
Arguments prim_step_prob {_} _ _ _ _ _.

Section prob_language.
  Context {Λ : probLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.

  Definition prob_lang_mixin : LanguageMixin (@of_val Λ) to_val prim_step.
  Proof.
    split.
    - apply prob_language_mixin.
    - apply prob_language_mixin.
    - apply prob_language_mixin.
  Qed.

  Canonical Structure prob_lang : language := Language prob_lang_mixin.

  Class ProbLanguageCtx (K : expr Λ → expr Λ) := {
    pfill_LanguageCtx : LanguageCtx K;
    pfill_prob e1 σ1 e2 σ2 efs : 
      to_val e1 = None →
      prim_step_prob e1 σ1 e2 σ2 efs = 
      prim_step_prob (K e1) σ1 (K e2) σ2 efs
  }.

  Inductive prim_step_result :=
  | prim_res_step : expr Λ → state Λ → list (expr Λ) → prim_step_result
  | prim_res_irred.

  Definition ival_prim_step e1 σ1 : ival (prim_step_result).
    destruct (ClassicalEpsilon.excluded_middle_informative (reducible e1 σ1)); last first.
    - unshelve (eexists).
      * apply [countType of unit].
      * intros; apply 1%R.
      * intros. apply (prim_res_irred).
      * intros [] => //=; auto with *.
    - set (ty := Countable.Pack (mixin_prim_step_count _ _ _ _ (prob_language_mixin Λ) e1 σ1)
                                { esf: expr Λ * state Λ * list (expr Λ) |
                                  prim_step e1 σ1 (esf.1.1) (esf.1.2) (esf.2) }).
        unshelve (eexists).
      * apply ty.
      * intros [esf Hpf].
        exact (prim_step_prob e1 σ1 (esf.1.1) (esf.1.2) (esf.2)).
      * intros [esf Hpf].
        exact (prim_res_step (esf.1.1) (esf.1.2) (esf.2)).
      * abstract (intros [[[e2 σ2] efs] Hpf];
          apply (mixin_prim_step_nonneg _ _ _ _ (prob_language_mixin Λ))).
  Defined.

  Lemma ivdist_prim_step_sum1 e1 σ1: 
    is_series (countable_sum (ival.val (ival_prim_step e1 σ1))) 1%R.
  Proof.
    rewrite /ival_prim_step.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|]; last first.
    - rewrite //=. 
      apply Series_correct'; last first.
      { eexists. apply finite.SeriesF_is_seriesC. }
      rewrite finite.SeriesC_SeriesF finite.SeriesF_big_op.
      { rewrite /index_enum [@Finite.enum]unlock //= big_cons big_nil //=. nra. }
    - rewrite //=.
      eapply is_seriesC_ext;
        last eapply (mixin_prim_step_sum1 _ _ _ _ (prob_language_mixin Λ) e1 σ1).
      * intros [[[e2 σ2] efs] Hpf] => //=.
      * eauto.
  Qed.

  Definition ivdist_prim_step e1 σ1 : ivdist (prim_step_result) :=
    {| ivd_ival := ival_prim_step e1 σ1; val_sum1 := ivdist_prim_step_sum1 e1 σ1 |}.

  Lemma ival_stuck_irred_nonval e σ :
    In_isupport prim_res_irred (ival_prim_step e σ) →
    irreducible e σ.
  Proof.
    rewrite /ival_prim_step.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
    - rewrite /irreducible. intros. apply not_reducible; eauto.
    - intros (x&Hind&?). rewrite //= in Hind.
      destruct x. congruence.
  Qed.

  Lemma ival_red_non_stuck' e σ:
    reducible e σ →
    ¬ (∃ i, ind (ival_prim_step e σ) i = prim_res_irred). 
  Proof.
    rewrite /ival_prim_step.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=.
    intros (e2&σ2&efs&Hstep) ([]&?); congruence.
  Qed.
      
  Lemma ival_red_non_stuck e σ:
    reducible e σ →
    ¬ (In_isupport prim_res_irred (ival_prim_step e σ)).
  Proof.
    intros ? (i&?&?); eapply ival_red_non_stuck'; eauto.
  Qed.

  Lemma ival_non_stuck_red e σ e' σ' efs:
    (reducible e σ ∨ to_val e = None) →
    (In_isupport (prim_res_step e' σ' efs) (ival_prim_step e σ)) →
    prim_step e σ e' σ' efs.
  Proof.
    intros Hred.
    rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
    - rewrite //=. intros ([]&Hind&?). rewrite //= in Hind.
    - rewrite //=. intros (m&Hind&?). rewrite //= in Hind.
      destruct m. inversion Hind; subst; eauto.
  Qed.

  Lemma ivdist_non_stuck_red e σ e' σ' efs:
    (In_isupport (prim_res_step e' σ' efs) (ival_prim_step e σ)) →
    (prim_step e σ e' σ' efs).
  Proof.
    specialize (ival_non_stuck_red e σ e' σ' efs).
    rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => Hpre //=; last first.
    - intros (x&Hind&?). rewrite //= in Hind.
    - rewrite //=. intros. eapply Hpre; eauto.
  Qed.

  Lemma ivdist_step_idx' e1 σ1 e2 σ2 efs:
    prim_step e1 σ1 e2 σ2 efs →
    ∃ i, ind (ivdist_prim_step e1 σ1) i = prim_res_step e2 σ2 efs
         ∧ (ival.val (ivdist_prim_step e1 σ1) i = prim_step_prob e1 σ1 e2 σ2 efs)%R.
  Proof.
    intros Hstep.
    rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
    * exfalso. eapply Hnr. do 3 eexists; eauto.
    * unshelve (eexists).
      { exists (e2, σ2, efs) => //=. }
      rewrite //=.
  Qed.

  Lemma ivdist_step_idx e1 σ1 e2 σ2 efs:
    prim_step e1 σ1 e2 σ2 efs →
    ∃ i, ind (ivdist_prim_step e1 σ1) i = prim_res_step e2 σ2 efs
         ∧ (ival.val (ivdist_prim_step e1 σ1) i > 0)%R.
  Proof.
    intros Hstep.
    edestruct ivdist_step_idx' as (i&?&Heq); eauto; exists i; split; auto.
    rewrite Heq. by apply (prob_language_mixin).
  Qed.

  Lemma irred_non_val_stuck_ivdist e1 σ1:
    irreducible e1 σ1 →
    In_isupport prim_res_irred (ivdist_prim_step e1 σ1).
  Proof.
    intros Hirred.
    rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
    - exists (); split => //=. nra.
    - exfalso. destruct Hr as (?&?&?&?). eapply Hirred; eauto. 
  Qed.

  Definition pidist_prim_step e1 σ1 : pidist (prim_step_result).
    unshelve (eexists).
    - unshelve (eexists).
      * exact (λ x, (ival_prim_step e1 σ1) = x).
      * eexists; eauto. 
    - abstract (intros ? <-; apply ivdist_prim_step_sum1).
  Defined.

  Inductive step_result :=
  | res_step : list (expr Λ) → state Λ → step_result
  | res_stuck.
    
  Fixpoint tpool_step (tl tp: list (expr Λ)) (σ: state Λ) : pidist step_result :=
    match tp with
    | [::] => mret res_stuck
    | e :: tp' =>
      pidist_union
        (r ← pidist_prim_step e σ;
           match r with
           | prim_res_step e' σ' efs => mret (res_step (tl ++ e' :: tp' ++ efs) σ')
           | prim_res_irred => mret res_stuck
           end)
        ((tpool_step (tl ++ [::e]) tp' σ))
    end.
                        
  Fixpoint tpool_stepN (n: nat) (tp: list (expr Λ)) (σ: state Λ): pidist (step_result) :=
    match n with
    | O => mret (res_step tp σ)
    | S n' =>
      r ← (tpool_step [::] tp σ);
        match r with
        | res_stuck => mret (res_stuck)
        | res_step tp' σ' =>
          tpool_stepN n' tp' σ'
        end
    end.
                     
  Definition trace := list (cfg prob_lang).

  Definition scheduler := trace → nat.

  Inductive trace_step (sch: scheduler) (tr1 tr2 : trace) : Prop :=
    | trace_active_step i ρ1 ρ2 tr0:
          sch tr1 = i →
          tr1 = tr0 ++ [::ρ1] →
          tr2 = tr0 ++ (ρ1 :: ρ2 :: nil) →
          istep i ρ1 ρ2 →
          trace_step sch tr1 tr2
    | trace_stutter_step i ρ1 tr0:
        sch tr1 = i →
        (¬ ∃ ρ2, istep i ρ1 ρ2) →
        tr1 = tr0  ++ [::ρ1] →
        tr2 = tr0  ++ [ρ1; ρ1] →
        trace_step sch tr1 tr2.
      
  Definition ivdist_tpool_stepi i (tp: list (expr Λ)) (σ: state Λ) : ivdist (step_result) :=
    match (tp !! i) with
    | None => mret res_stuck
    | Some e =>
      r ← ivdist_prim_step e σ;
        match r with
        | prim_res_step e' σ' efs =>
          mret (res_step (list.take i tp ++ (e' :: list.drop (S i) tp) ++ efs) σ')
        | prim_res_irred => mret res_stuck
        end
    end.
      
  Definition ivdist_trace_step (s: scheduler) (tr: trace) (tp: list (expr Λ)) (σ: state Λ)
    : ivdist (list (expr Λ) * state Λ) :=
      r ← (ivdist_tpool_stepi (s (tr ++ [::(tp, σ)])) tp σ);
        match r with
        | res_step tp' σ' => mret (tp', σ')
        | res_stuck => mret (tp, σ)
        end.
                                            
  Fixpoint ivdist_trace_stepN_aux s tr tp σ n :=
    match n with
    | O => mret (tp, σ)
    | S n' => 
      r ← ivdist_trace_step s tr tp σ;
      ivdist_trace_stepN_aux s (tr ++ [::(tp, σ)])  (fst r) (snd r) n'
    end.

  Definition ivdist_tpool_stepN s tp σ n :=
    ivdist_trace_stepN_aux s [::] tp σ n.

  Definition terminates s tr n :=
    ∀ tr' cfg n', n ≤ n' → nsteps (trace_step s) n' tr (tr' ++ [::cfg]) →
               ∃ v tp, (fst cfg) = (of_val v :: tp).

  Lemma terminates_S s tr cfg cfg' i n :
    terminates s (tr ++ [::cfg]) (S n) →
    s (tr ++ [::cfg]) = i →
    istep i cfg cfg' →
    terminates s (tr ++ (cfg :: cfg' :: nil)) n.
  Proof.
    intros Hterm Hlookup Hi tr' cfg'' n'' Hle Hsteps.
    eapply (Hterm _ _ (S n'')); first omega.
    econstructor; [ econstructor |]; eauto.
  Qed.

  Lemma istep_idx_length i (cfg: language.cfg prob_lang) cfg':
    istep i cfg cfg' → (i < length (fst cfg))%nat.
  Proof.
    inversion 1; subst. rewrite app_length //=. omega. 
  Qed.

  Lemma ivdist_prim_step_val_mret e σ:
    language.to_val e <> None →
    eq_ivd (ivdist_prim_step e σ) (mret (prim_res_irred)).
  Proof.
    intros Hval.
    rewrite /eq_ivd//=.
    rewrite /ival_prim_step.
    destruct ClassicalEpsilon.excluded_middle_informative as [r|?].
    { exfalso. destruct r as (?&?&?&?). eapply Hval. eapply language.val_stuck; eauto. }
    rewrite /language.to_val//= in Hval.
    destruct (to_val e); last congruence.
    rewrite //=.
    eapply eq_ival_quasi_refl.
  Qed.

  Lemma terminates_stutter_None s tr cfg i n :
    terminates s (tr ++ [::cfg]) (S n) →
    s (tr ++ [::cfg]) = i →
    (fst cfg !! i = None) →
    terminates s (tr ++ (cfg :: cfg :: nil)) n.
  Proof.
    intros Hterm Hsch Hi tr' cfg'' n'' Hle Hsteps.
    eapply (Hterm _ _ (S n'')); first omega.
    econstructor; last eauto.
    eapply trace_stutter_step; eauto.
    intros (cfg'&Hstep).
    assert (length (fst cfg) <= i)%nat.
    { eapply lookup_ge_None_1; eauto. }
    feed pose proof (istep_idx_length i cfg cfg'); eauto.
    omega.
  Qed.

  Lemma terminates_stutter_value s tr cfg i ei n :
    terminates s (tr ++ [::cfg]) (S n) →
    s (tr ++ [::cfg]) = i →
    (fst cfg !! i = Some ei) →
    (to_val ei <> None) →
    terminates s (tr ++ (cfg :: cfg :: nil)) n.
  Proof.
    intros Hterm Hsch Hi Hval tr' cfg'' n'' Hle Hsteps.
    eapply (Hterm _ _ (S n'')); first omega.
    econstructor; last eauto.
    eapply trace_stutter_step; eauto.
    intros (cfg'&Hstep).
    inversion Hstep.
    exfalso; eapply Hval. eapply language.val_stuck; eauto.
    subst.
    rewrite list_lookup_middle in Hi; eauto.
    inversion Hi; subst; eauto.
  Qed.
  
  Lemma terminates_mono s tr n n' :
    n ≤ n' →
    terminates s tr n →
    terminates s tr n'.
  Proof.
    intros Hle Hterm.
    intros tr' cfg n'' Hle'' Hnsteps.
    eapply (Hterm _ _ n''); eauto.
    omega.
  Qed.
    
  Definition terminating s tr := ∃ n, terminates s tr n.

  Lemma ivdist_prim_step_primitive e σ: ival_primitive (ivdist_prim_step e σ).
  Proof.
   rewrite //=/ival_prim_step.
   destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
   - rewrite /ival_primitive => //=. intros [] [] => //=.
   - rewrite /ival_primitive => //=.
     intros (((?&?)&?)&?) (((?&?)&?)&?) Heq.
     apply sval_inj_pi => //=.
     inversion Heq; eauto.
  Qed.

  Global Instance prob_lang_ctx_proj K `{ProbLanguageCtx K} : LanguageCtx K.
  Proof. apply pfill_LanguageCtx. Qed.

  Lemma ivdist_val_step e1 σ1 e2 σ2 efs i1:
    (reducible e1 σ1 ∨ to_val e1 = None) →
    ind (ivdist_prim_step e1 σ1) i1 = prim_res_step e2 σ2 efs →
    ival.val (ivdist_prim_step e1 σ1) i1 = prim_step_prob e1 σ1 e2 σ2 efs.
  Proof.
    intros Hred. revert i1.
    rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; [].
    rewrite //= => i Heq.
    destruct i as (((?&?)&?)&?).
    inversion Heq; subst; eauto.
  Qed.
  
  Lemma ivdist_stuck_val_1 e σ i:
    ind (ivdist_prim_step e σ) i = prim_res_irred →
    ival.val (ivdist_prim_step e σ) i = 1%R.
  Proof.
    move: i. rewrite /ivdist_prim_step/ival_prim_step//=.
    destruct ClassicalEpsilon.excluded_middle_informative as [Hr|Hnr] => //=; last first.
    intros (?&?). congruence.
  Qed.

  Lemma ivdist_bind_eq_post_fill K `{!ProbLanguageCtx K} e1 σ1:
    (reducible e1 σ1 ∨ to_val e1 = None) →
    eq_ivd (ivdist_prim_step (K e1) σ1)
                 (x ← (ivdist_prim_step e1 σ1);
                  mret (match x with
                        | prim_res_step e2 efs σ => prim_res_step (K e2) efs σ
                        | prim_res_irred => prim_res_irred
                        end)).
  Proof.
    intros Hred.
    symmetry. apply eq_ival_primitive_fmap_bij.
    - apply ivdist_prim_step_primitive. 
    - apply ivdist_prim_step_primitive. 
    - intros v Hin. destruct v.
      * eapply ival_non_stuck_red in Hin; eauto.
        edestruct ivdist_step_idx as (i&?&?); last first.
        { exists i; split; eauto. }
        by apply fill_step.
      * destruct Hred.
        ** exfalso.
           eapply ival_red_non_stuck; eauto.
        ** apply irred_non_val_stuck_ivdist.
           *** apply ival_stuck_irred_nonval in Hin.
               apply irreducible_fill; eauto.
    - intros v1 v1' ??.
      destruct v1, v1' => //=.
      inversion 1; f_equal. apply: (@fill_inj _ K); auto. 
    - rewrite /ivdist_prim_step.
      intros v2 Hin.
      destruct v2 as [e σ2 efs |].
      ** efeed pose proof (ival_non_stuck_red); [| eauto |].
         { left. rewrite //= in Hin. apply ivdist_non_stuck_red in Hin.
           do 3 eexists; eauto.
         }
        rewrite //= in Hin.  edestruct (@fill_step_inv) as (e'&?&?); eauto; subst; try apply _.
           *** destruct Hred; auto. by eapply reducible_not_val; eauto.
           *** rewrite //=. exists (prim_res_step e' σ2 efs); split; eauto.
               edestruct ivdist_step_idx as (i&?&?); last first.
               { exists i; split; eauto. }
               eauto.
      ** destruct Hred as [Hred|Hnonval].
         *** exfalso. eapply ival_red_non_stuck; last by eauto.
             edestruct Hred as (e2&σ2&efs&Hstep).
             exists (K e2), σ2, efs.
             apply fill_step; eauto.
         *** exists prim_res_irred; split; auto.
             apply ival_stuck_irred_nonval in Hin as Hirred. 
             apply irred_non_val_stuck_ivdist; auto.
             intros e2 σ2 efs Hstep. by apply (Hirred (K e2) σ2 efs), fill_step.
    - intros i1 i2. 
      case_eq (ind (ivdist_prim_step e1 σ1) i1).
      * intros e2 σ2 efs Hind1 Hind2.
        erewrite ivdist_val_step; eauto; last first.
        { destruct Hred as [Hred|Hnonval].
          ** left. edestruct Hred as (?&?&?&?); do 3 eexists. by apply fill_step.
          ** right.  by apply fill_not_val.
        }
        erewrite ivdist_val_step; eauto.
        rewrite -pfill_prob //=.
        destruct Hred; auto. eapply reducible_not_val; eauto.
      * intros. destruct Hred.
        ** exfalso. eapply ival_red_non_stuck'; eauto.
        ** by rewrite ?ivdist_stuck_val_1.
  Qed.


  (* TODO: many of these proofs can be simplified, since reducible e1 σ1 implies
     e1 is not a value, so the left part of the disjunction is not necessary; however
     this disjunction was added on after the fact. *)
  Lemma ivdist_bind_coupling {X} K `{!ProbLanguageCtx K} e1 σ1 (I: pidist X) P:
    ∀ (Ic: irrel_couplingP (ivdist_prim_step e1 σ1) I P),
      (reducible e1 σ1 ∨ to_val e1 = None) →
      irrel_couplingP (ivdist_prim_step (K e1) σ1) I
                      (λ x y,
                       (match x with
                        | prim_res_step e2 σ efs =>
                          ∃ e2' pf, e2 = K e2' ∧ prim_step e1 σ1 e2' σ efs ∧
                                    ival.In_isupport (exist _ (prim_res_step e2' σ efs, y) pf) Ic
                       | prim_res_irred => ∃ pf,
                          ival.In_isupport (exist _ (prim_res_irred, y) pf) Ic
                        end)).
  Proof.
    intros. 
      eapply irrel_coupling_proper.
      { symmetry. apply: ivdist_bind_eq_post_fill; eauto. }
      { apply pidist_right_id. } 
      eapply irrel_coupling_bind.
      { apply (irrel_coupling_support _ _ _ Ic).  }
      intros x' y' HP.
      eapply irrel_coupling_mret.
      rewrite //= in HP.
      destruct HP as (Hpf&Hin1&Hin2&HIn3).
      destruct x' => //=.
      - do 2 eexists; repeat split; eauto.
        eapply ival_non_stuck_red; eauto.
      - eexists; eauto. 
  Qed.

  Definition Kinv K `{LanguageCtx prob_lang K} : expr Λ → expr Λ.
    intros e. destruct (ClassicalEpsilon.excluded_middle_informative (∃ e', K e' = e)) as [Heq|Hneq].
    - apply ClassicalEpsilon.constructive_indefinite_description in Heq as (e'&?).
      exact e'.
    - exact e.
  Defined.
  
  Lemma Kinv_K K `{!LanguageCtx K} e:
    Kinv K (K e) = e.
  Proof.
    rewrite /Kinv.
    destruct ClassicalEpsilon.excluded_middle_informative as [?|Hfalse].
    - destruct ClassicalEpsilon.constructive_indefinite_description.
        by apply fill_inj.
    - exfalso. apply Hfalse. eauto.
  Qed.
  
  Lemma ivdist_bind_eq_post_fill_inv K `{!ProbLanguageCtx K} e1 σ1:
    (reducible e1 σ1 ∨ to_val e1 = None) →
    eq_ivd (ivdist_prim_step e1 σ1)
           (x ← (ivdist_prim_step (K e1) σ1);
              mret (match x with
                    | prim_res_step e2 efs σ => prim_res_step (Kinv K e2) efs σ
                    | prim_res_irred => prim_res_irred
                    end)).
  Proof.
    intros Hred.
    setoid_rewrite ivdist_bind_eq_post_fill; auto.
    rewrite /eq_ivd.
    setoid_rewrite ival.ival_bind_mret_mret.
    setoid_rewrite <-ival.ival_right_id at 1.
    eapply ival.ival_bind_congr; first by reflexivity.
    intros [|] => //=; rewrite ?Kinv_K; reflexivity.
  Qed.

  
  Lemma ivdist_bind_inv_coupling {X} K `{!ProbLanguageCtx K} e1 σ1 (I: pidist X) P:
    ∀ (Ic: irrel_couplingP (ivdist_prim_step (K e1) σ1) I P),
      (reducible e1 σ1 ∨ to_val e1 = None) →
      irrel_couplingP (ivdist_prim_step e1 σ1) I
                      (λ x y,
                       (match x with
                        | prim_res_step e2 σ efs =>
                         ∃ pf, prim_step (K e1) σ1 (K e2) σ efs ∧
                               ival.In_isupport (exist _ (prim_res_step (K e2) σ efs, y) pf) Ic
                       | prim_res_irred => ∃ pf,
                          ival.In_isupport (exist _ (prim_res_irred, y) pf) Ic
                        end)).
  Proof.
    intros Ic Hred. 
      eapply irrel_coupling_proper.
      { symmetry. apply: ivdist_bind_eq_post_fill_inv; eauto. }
      { apply pidist_right_id. } 
      eapply irrel_coupling_bind.
      { apply (irrel_coupling_support _ _ _ Ic).  }
      intros x' y' HP.
      eapply irrel_coupling_mret.
      rewrite //= in HP.
      destruct HP as (Hpf&Hin1&Hin2&HIn3).
      destruct x' as [e s l|] => //=.
    - assert (reducible (K e1) σ1 ∨ to_val (K e1) = None).
      { destruct Hred as [Hred|Hnonval].
        * left. edestruct Hred as (?&?&?&?). do 3 eexists.
          apply: fill_step; eauto.
        * right. by apply fill_not_val.
      } 
        assert (prim_step (K e1) σ1 e s l) as Hstep1.
        { eapply ival_non_stuck_red; eauto. }

        assert (K (Kinv K e) = e) as Hrewrite.
        { eapply fill_step_inv in Hstep1 as (e0&?&?); last first.
          { destruct Hred; auto; eauto; (eapply reducible_not_val); eauto. }

          subst. rewrite Kinv_K. done.
        }

        rewrite Hrewrite.
        do 2 eexists; repeat split; eauto.
    - exists Hpf. auto.
  Qed.


End prob_language.

Arguments prob_lang : clear implicits.
Coercion prob_lang : probLanguage >-> language.

(* See the explanation in ectxLanguage *)

Definition LanguageOfProb (Λ : probLanguage) : language :=
  let '@ProbLanguage E V St of_val to_val prim_step prim_step_prob mix := Λ in
  @Language E V St of_val to_val _
    (@prob_lang_mixin (@ProbLanguage E V St of_val to_val prim_step prim_step_prob mix)).