Require Import Reals Psatz ClassicalEpsilon.
(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import prob_language.
From discprob.prob Require Import prob countable.
From mathcomp Require Import ssreflect bigop choice fintype finset ssrbool eqtype.
Set Default Proof Using "Type".

(* TAKE CARE: When you define an [ectxLanguage] canonical structure for your
language, you need to also define a corresponding [language] canonical
structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
file for doing that. *)

Section ectx_language_mixin.
  Context {expr val ectx state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → expr → state → list expr → Prop).
  Context (head_step_prob : expr → state → expr → state → list expr → R).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 e2 σ2 efs :
      head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);

    (* There are a whole lot of sensible axioms (like associativity, and left and
    right identity, we could demand for [comp_ectx] and [empty_ectx]. However,
    positivity suffices. *)
    mixin_ectx_positive K1 K2 :
      comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx;

    mixin_step_by_val K K' e1 e1' σ1 e2 σ2 efs :
      fill K e1 = fill K' e1' →
      to_val e1 = None →
      head_step e1' σ1 e2 σ2 efs →
      ∃ K'', K' = comp_ectx K K'';

    mixin_step_by_val_eq K K' e1 e1' σ1 e2 e2' σ2 σ2' efs efs' :
      fill K e1 = fill K' e1' →
      head_step e1 σ1 e2 σ2 efs →
      head_step e1' σ1 e2' σ2' efs' →
      K = K';

    
    mixin_head_step_count e σ: 
      Countable.class_of { esf: expr * state * list expr |
                           head_step e σ (esf.1.1) (esf.1.2) (esf.2) };
    mixin_head_step_sum1 e σ:
        (∃ e' σ' efs, head_step e σ e' σ' efs) →
        is_series (countable_sum (λ t : Countable.Pack (mixin_head_step_count e σ)
                                        { esf: expr * state * list expr |
                                          head_step e σ (esf.1.1) (esf.1.2) (esf.2) },
                                    head_step_prob e σ
                                                   (fst (fst (sval t)))
                                                   (snd (fst (sval t)))
                                                   (snd (sval t)))) 1;
    mixin_head_step_nonneg : ∀ e1 σ1 e2 σ2 efs, (head_step_prob e1 σ1 e2 σ2 efs >= 0)%R;
    mixin_head_step_strict_gt :
    ∀ e1 σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs ↔ (head_step_prob e1 σ1 e2 σ2 efs > 0)%R

  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;
  head_step_prob : expr → state → expr → state → list expr → R;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step head_step_prob;

}.

Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments empty_ectx {_}.
Arguments comp_ectx {_} _ _.
Arguments fill {_} _ _%E.
Arguments head_step {_} _%E _ _%E _ _.
Arguments head_step_prob {_} _%E _ _%E _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma ectx_positive K1 K2 :
    comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val_eq K K' e1 e1' σ1 e2 e2' σ2 σ2' efs efs' :
      fill K e1 = fill K' e1' →
      head_step e1 σ1 e2 σ2 efs →
      head_step e1' σ1 e2' σ2' efs' →
      K = K'.
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K K' e1 e1' σ1 e2 σ2 efs :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step e1' σ1 e2 σ2 efs →
    ∃ K'', K' = comp_ectx K K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_step_count e σ:
    Countable.class_of { esf: expr Λ * state Λ * list (expr Λ) |
                           head_step e σ (esf.1.1) (esf.1.2) (esf.2) }.
  Proof. apply ectx_language_mixin. Defined.
  Lemma head_step_sum1 e σ:
    (∃ e' σ' efs, head_step e σ e' σ' efs) →
    is_series (countable_sum (λ t : Countable.Pack (head_step_count e σ)
                                                   { esf: expr Λ * state Λ * list (expr Λ) |
                                                     head_step e σ (esf.1.1) (esf.1.2) (esf.2) },
                                    head_step_prob e σ
                                                   (fst (fst (sval t)))
                                                   (snd (fst (sval t)))
                                                   (snd (sval t)))) 1.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_step_nonneg e1 σ1 e2 σ2 efs:
    (head_step_prob e1 σ1 e2 σ2 efs >= 0)%R.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_step_strict_gt e1 σ1 e2 σ2 efs:
    head_step e1 σ1 e2 σ2 efs ↔ (head_step_prob e1 σ1 e2 σ2 efs > 0)%R.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, head_step e σ e' σ' efs.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬head_step e σ e' σ' efs.
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ ∀ K e', e = fill K e' → head_irreducible e' σ.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (e1 : expr Λ) (σ1 : state Λ)
      (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 e2' σ2 efs → prim_step e1 σ1 e2 σ2 efs.

  Definition prim_step_prob (e1 : expr Λ) (σ1 : state Λ)
             (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)) : R :=
    (let s := 
         excluded_middle_informative
           (∃ (K : ectx Λ) (e1' e2' : expr Λ), e1 = fill K e1' ∧ e2 = fill K e2'
                                           ∧ head_step e1' σ1 e2' σ2 efs) in
     match s with
     | left Hhead =>
       let (K, Hhead1) := constructive_indefinite_description _ Hhead in
       let (e1', Hhead2) := constructive_indefinite_description _ Hhead1 in
       let (e2', _) := constructive_indefinite_description _ Hhead2 in
       head_step_prob e1' σ1 e2' σ2 efs
     | right _ => 0%R
     end).

  Definition prim_step_pickle e σ (esf: {esf : expr Λ * state Λ * list (expr Λ) |
                                         prim_step e σ esf.1.1 esf.1.2 esf.2}):
    nat.
  Proof.
    destruct esf as (esf&Hstep).
    destruct (excluded_middle_informative
                (∃ (K : ectx Λ) (e1' e2' : expr Λ),
                    e = fill K e1' ∧ esf.1.1 = fill K e2'
                    ∧ head_step e1' σ e2' esf.1.2 esf.2)) as [Hex|Hnex].
    - apply constructive_indefinite_description in Hex as (K&Hex).
      apply constructive_indefinite_description in Hex as (e1'&Hex).
      apply constructive_indefinite_description in Hex as (e2'&Hex).
      apply (@pickle (Countable.Pack (head_step_count e1' σ)
                                     { esf: expr Λ * state Λ * list (expr Λ) |
                                       head_step e1' σ e2' (esf.1.2) (esf.2)})).
      exists (e2', esf.1.2, esf.2); rewrite //=; abstract (intuition).
    - abstract (exfalso; eapply Hnex; inversion Hstep; do 3 eexists; split_and!; eauto).
  Defined.

  Definition prim_step_unpickle e σ (n: nat) :
    option {esf : expr Λ * state Λ * list (expr Λ) | prim_step e σ esf.1.1 esf.1.2 esf.2}.
  Proof.
    destruct (excluded_middle_informative
                (∃ (K : ectx Λ) (e1' e2' : expr Λ) σ' efs,
                    e = fill K e1' ∧ head_step e1' σ e2' σ' efs)) as [Hex|Hnex].
    - apply constructive_indefinite_description in Hex as (K&Hex).
      apply constructive_indefinite_description in Hex as (e1'&Hex).
      destruct (@unpickle (Countable.Pack (head_step_count e1' σ)
                                     { esf: expr Λ * state Λ * list (expr Λ) |
                                       head_step e1' σ (esf.1.1) (esf.1.2) (esf.2)}) n)
               as [s|].
      * destruct s as (esf&Hpf).
        apply Some. exists (fill K (esf.1.1), esf.1.2, esf.2).
        abstract (destruct Hex as (?&?&?&?); eexists; eauto; intuition).
      * apply None. 
    - apply None.
  Defined.

  Lemma pickle_primK e σ:
    ssrfun.pcancel (prim_step_pickle e σ) (prim_step_unpickle e σ).
  Proof.
    rewrite /prim_step_pickle/prim_step_unpickle//=.
    intros (esf&Hstep) => //=.
    destruct excluded_middle_informative as [Hex|Hnex]; last first.
    { 
      exfalso. apply Hnex. inversion Hstep.
      do 5 eexists. split_and!; eauto.
    }
    destruct constructive_indefinite_description as (K&?).
    destruct constructive_indefinite_description as (e1'&Hex'').
    destruct excluded_middle_informative as [Hex'|Hnex']; last first.
    { 
      exfalso. eapply Hnex'.
      destruct Hex'' as (?&?&?&?&?).
      inversion Hstep. subst.
      do 3 eexists; eauto.
    }
    destruct Hex'' as (e2'&σ'&efs&?&?).
    destruct constructive_indefinite_description as (K'&?).
    destruct constructive_indefinite_description as (e1''&?).
    destruct constructive_indefinite_description as (e2''&Hex''').
    assert (K' = K).
    { intuition. eapply step_by_val_eq.
      * transitivity e; eauto.
      * eauto.
      * eauto.
    }
    subst.
    assert (e1' = e1'').
    { intuition. eapply fill_inj. eauto. }
    subst.
    rewrite pickleK => //=.
    f_equal. apply sval_inj_pi => //=.
    intuition.
    destruct esf as [[? ?] ?].
    rewrite //=. subst.
    f_equal. f_equal. eauto.
  Qed.

  Lemma Ectx_step' K e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ????? [??? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Lemma map_legacy {A B: Type} (f: A → B) l:
    seq.map f l = List.map f l.
  Proof.  
    induction l => //=.
  Qed.

  Lemma ectx_count_mixin:
  ∀ (e : expr Λ) (σ : state Λ),
    Countable.class_of {esf : expr Λ * state Λ * list (expr Λ) | prim_step e σ esf.1.1 esf.1.2 esf.2}.
  Proof.
    intros e σ.
    split.
    - econstructor.
      * exists (λ x y, ClassicalEpsilon.excluded_middle_informative (x = y)).
        intros x y. destruct excluded_middle_informative; eauto; econstructor => //=.
      * eapply PcanChoiceMixin; eapply pickle_primK.
    - eapply PcanCountMixin; eapply pickle_primK.
  Qed.

  Definition ectx_prob_lang_mixin : ProbLanguageMixin of_val to_val prim_step prim_step_prob.
  Proof.
    unshelve (econstructor).
    - intros. apply ectx_count_mixin.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ????? [??? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
    - intros e1 σ1 (e2&σ2&efs&Hprim).
      inversion Hprim as [K e1' e2' ? ? ?]; subst.
      feed pose proof (head_step_sum1 e1' σ1) as His.
      { do 3 eexists; eauto. }
      rewrite -(is_series_unique _ _ His).
      unshelve (edestruct (@rearrange.countable_series_rearrange_covering
                             (Countable.Pack (ectx_count_mixin (fill K e1') σ1)
                                             {esf : expr Λ * state Λ * list (expr Λ) |
                                              prim_step (fill K e1') σ1 esf.1.1 esf.1.2 esf.2})
                             (Countable.Pack (head_step_count e1' σ1)
                                             {esf : expr Λ * state Λ * list (expr Λ) |
                                              head_step e1' σ1 esf.1.1 esf.1.2 esf.2})
                          ) as (His1&His2));
       last (eapply is_seriesC_ext; last eapply His2).
      * intros (esf&Hstep).
        assert (Hfill: ∃ e2'', fill K e2'' = esf.1.1 ∧
                        head_step e1' σ1 e2'' esf.1.2 esf.2).
        { 
        inversion Hstep as [K' e1'' e2''].
          assert (K = K').
          { abstract (intuition; eapply step_by_val_eq; eauto). }
          assert (e1' = e1'').
          { abstract (subst; eapply fill_inj; eauto). }
          exists e2''; 
            abstract (rewrite //=; subst; eauto).
        }
        apply constructive_indefinite_description in Hfill as (e2''&?&?).
        exists (e2'', esf.1.2, esf.2); auto.
      * exact 1.
      * intros (esf1&Hstep1) (esf2&Hstep2) Hnz => //=.
        destruct Hstep1.
        destruct esf1 as [[? ?] ?].
        destruct esf2 as [[? ?] ?].
        rewrite //=.
        destruct constructive_indefinite_description as (e2''&?&?).
        destruct constructive_indefinite_description as (e2'''&?&?).
        inversion 1. subst. eapply sval_inj_pi.
        rewrite //=.
      * intros (esf&Hstep1) Hnz.
        unshelve (eexists).
        { exists (fill K (esf.1.1), esf.1.2, esf.2).
          { econstructor => //=. }
        }
        rewrite //=.
        destruct esf as [[? ?] ?] => //=.
        destruct constructive_indefinite_description as (e2''&?&?).
        apply sval_inj_pi => //=. 
        subst; f_equal.
        f_equal.
        eapply fill_inj; eauto.
      * eapply is_seriesC_ext; try eassumption.
        intros n => //=. rewrite Rabs_right //=. apply head_step_nonneg.
      * intros (esf&Hstep) => //=. 
        destruct constructive_indefinite_description as (e2''&?&?).
        rewrite /prim_step_prob.
        destruct excluded_middle_informative as [?|Hnex].
        ** destruct (constructive_indefinite_description) as (K'&?).
           destruct (constructive_indefinite_description) as (e1''&?).
           destruct (constructive_indefinite_description) as (e2'''&Hfill1'&Hfill2'&Hstep').

           assert (K = K') as HeqK.
           { eapply (step_by_val_eq K K' e1' e1'');
               eauto; congruence. }
           assert (e1' = e1'') as Heqe.
           { subst. eapply fill_inj; eauto.  }
           subst.
           rewrite //=.
           f_equal.
           eapply fill_inj; eauto. 
           transitivity (esf.1.1); eauto.
        ** exfalso; eapply Hnex. do 3 eexists; intuition; eauto.
    - intros. rewrite /prim_step_prob.
      destruct (excluded_middle_informative); last by nra.
      repeat destruct (constructive_indefinite_description).
      apply ectx_language_mixin.
    - intros ?????. split.
      * intros Hstep. rewrite /prim_step_prob.
        destruct (excluded_middle_informative) as [|Hn].
        ** repeat destruct (constructive_indefinite_description).
           apply ectx_language_mixin.
           firstorder.
        ** exfalso. edestruct Hn.
           inversion Hstep. do 3 eexists; split_and!; eauto.
      * rewrite /prim_step_prob. intros Hgt.
        destruct (excluded_middle_informative) as [|Hn].
        ** do 2 destruct (constructive_indefinite_description).
           destruct constructive_indefinite_description as (?&?&?&?).
           econstructor; eauto.
        ** nra.
  Qed.
  Canonical Structure ectx_prob_lang : probLanguage := ProbLanguage ectx_prob_lang_mixin.
  Canonical Structure ectx_lang := LanguageOfProb ectx_prob_lang. 

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ' efs,
      head_step e σ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  (* Some lemmas about this language *)
  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma head_prim_step e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step e1 σ1 e2 σ2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  Program Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.

  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    intros (e'&σ'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    move=>[] ? Hirr ?. split; first done.
    apply prim_head_irreducible; last done.
    apply (Hirr empty_ectx). by rewrite fill_empty.
  Qed.

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step e1 σ1 e2 σ2 efs →
    head_step e1 σ1 e2 σ2 efs.
  Proof.
    intros (e2''&σ2''&efs''&?) [K e1' e2' -> -> Hstep].
    erewrite (step_by_val_eq K empty_ectx e1' (fill K e1'));
      eauto using fill_empty, fill_not_val, val_stuck.
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step_prob e1 σ1 e2 σ2 efs :
    head_reducible e1 σ1 →
    sub_redexes_are_values e1 →
    prim_step_prob e1 σ1 e2 σ2 efs = head_step_prob e1 σ1 e2 σ2 efs.
  Proof.
    intros Hred Hsub. rewrite /prim_step_prob.
    destruct ClassicalEpsilon.excluded_middle_informative as [?|Hnot]; last first.
    {
      edestruct head_step_nonneg; eauto.
      exfalso. apply Hnot.
      exists empty_ectx. do 2 eexists; rewrite ?fill_empty; split_and!; eauto.
      apply head_step_strict_gt; auto.
    }

    destruct (ClassicalEpsilon.constructive_indefinite_description) as (K&?).
    destruct (ClassicalEpsilon.constructive_indefinite_description) as (e1'&?).
    destruct (ClassicalEpsilon.constructive_indefinite_description) as (e2'&?&?&?).
    subst. rewrite /sub_redexes_are_values in Hsub.
    assert (K = empty_ectx).
    { eapply Hsub; eauto. eapply val_head_stuck; eauto. }
    subst; rewrite ?fill_empty => //=.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 e2'' σ2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
    - eauto using fill_inj. 
  Qed.

  Global Instance ectx_lang_ctx_prob K : ProbLanguageCtx (fill K).
  Proof.
    split.
    - apply: _.
    - intros. rewrite //=/prim_step_prob//=.
      destruct (excluded_middle_informative) as [|Hn] => //=;
      destruct (excluded_middle_informative) as [|HnK] => //=.
      ** destruct (constructive_indefinite_description) as (K'&?).
         destruct (constructive_indefinite_description) as (e1''&?).
         destruct (constructive_indefinite_description) as (e2''&Hfill1'&Hfill2'&Hstep).

         destruct (constructive_indefinite_description) as (K''&?).
         destruct (constructive_indefinite_description) as (e1'''&?).
         destruct (constructive_indefinite_description) as (e2'''&Hfill1''&Hfill2''&Hstep').

         rewrite Hfill1' fill_comp in Hfill1''.
         rewrite Hfill2' fill_comp in Hfill2''.
         assert (comp_ectx K K' = K'').
         { eapply step_by_val_eq.
           * apply Hfill1''.
           * eauto.
           * eauto. 
         }
         subst.
         f_equal; auto.
         *** eapply fill_inj; eauto.
         *** eapply fill_inj; eauto.
      ** destruct (constructive_indefinite_description) as (K'&?).
         destruct (constructive_indefinite_description) as (e1''&?).
         destruct (constructive_indefinite_description) as (e2''&Hfill1'&Hfill2'&Hstep).

         exfalso; eapply HnK.
         exists (comp_ectx K K'), e1'', e2''; split_and!; subst.
         *** apply fill_comp. 
         *** apply fill_comp. 
         *** eauto.
      ** destruct (constructive_indefinite_description) as (K'&?).
         destruct (constructive_indefinite_description) as (e1''&?).
         destruct (constructive_indefinite_description) as (e2''&Hfill1'&Hfill2'&Hstep).

         exfalso; eapply Hn.
         edestruct step_by_val as (K''&Heq); try apply Hstep; eauto.
         subst.
         rewrite -?fill_comp in Hfill1' Hfill2'.
         apply fill_inj in Hfill1'.
         apply fill_inj in Hfill2'.
         exists K'', e1'', e2''; repeat split; auto.
  Qed.

  Lemma det_head_step_pure_exec (P : Prop) e1 e2 :
    (∀ σ, P → head_reducible e1 σ) →
    (∀ σ1 e2' σ2 efs,
      P → head_step e1 σ1 e2' σ2 efs → σ1 = σ2 ∧ e2=e2' ∧ efs = []) →
    PureExec P e1 e2.
  Proof.
    intros Hp1 Hp2. split.
    - intros σ ?. destruct (Hp1 σ) as (e2' & σ2 & efs & ?); first done.
      eexists e2', σ2, efs. by apply head_prim_step.
    - intros σ1 e2' σ2 efs ? ?%head_reducible_prim_step; eauto.
  Qed.

  Global Instance pure_exec_fill K e1 e2 φ :
    PureExec φ e1 e2 →
    PureExec φ (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.

End ectx_language.

Arguments ectx_prob_lang : clear implicits.
Arguments ectx_lang : clear implicits.
Coercion ectx_prob_lang : ectxLanguage >-> probLanguage.
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition ProbLanguageOfEctx (Λ : ectxLanguage) : probLanguage :=
  let '@EctxLanguage E V C St of_val to_val empty comp fill head head_prob mix := Λ in
  @ProbLanguage E V St of_val to_val _ _
    (@ectx_prob_lang_mixin (@EctxLanguage E V C St of_val to_val empty comp fill head head_prob mix)).
