Require Import Reals.
Require ClassicalEpsilon.
(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language prob_language ectx_language.
From mathcomp Require Import ssreflect bigop choice fintype finset ssrbool eqtype.
From discprob Require Import bigop_ext.
From discprob.prob Require Import prob countable.
Set Default Proof Using "Type".

(* TAKE CARE: When you define an [ectxiLanguage] canonical structure for your
language, you need to also define a corresponding [language] and [ectxLanguage]
canonical structure for canonical structure inference to work properly. You
should use the coercion [EctxLanguageOfEctxi] and [LanguageOfEctx] for that, and
not [ectxi_lang] and [ectxi_lang_ectx], otherwise the canonical projections will
not point to the right terms.

A full concrete example of setting up your language can be found in [heap_lang].
Below you can find the relevant parts:

  Module heap_lang.
    (* Your language definition *)

    Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
    Proof. (* ... *) Qed.
  End heap_lang.

  Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
  Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
  Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.
*)

Section ectxi_language_mixin.
  Context {expr val ectx_item state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → expr → state → list expr → Prop).
  Context (head_step_prob : expr → state → expr → state → list expr → R).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);
    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    mixin_head_ctx_step_val Ki e σ1 e2 σ2 efs :
      head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e);

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
End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;

  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;
  head_step_prob : expr → state → expr → state → list expr → R;
  ectxi_language_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step head_step_prob
}.

Arguments EctxiLanguage {_ _ _ _ _ _ _ _ _} _.
Arguments of_val {_} _%V.
Arguments to_val {_} _%E.
Arguments fill_item {_} _ _%E.
Arguments head_step {_} _%E _ _%E _ _.
Arguments head_step_prob {_} _%E _ _%E _ _.

Lemma filter_ssr_filter {A} (P: A → Prop) (f: ∀ x, Decision (P x)) (l: list A):
  filter f l = seq.filter (λ x, is_left (f x)) l.
Proof.
  induction l => //=.
  rewrite /filter//=.
  destruct (f a) => //=.
  f_equal; eauto.
Qed.

Lemma fin_sum1_helper expr state
  (head_step_prob : expr → state → expr → state → list expr → R)
  (head_step : expr → state → expr → state → list expr → Prop)
  (head_step_nonneg : ∀ e1 σ1 e2 σ2 efs, (head_step_prob e1 σ1 e2 σ2 efs >= 0)%R)
  (head_step_strict_gt :
    ∀ e1 σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs ↔ (head_step_prob e1 σ1 e2 σ2 efs > 0)%R):
  (∀ e1 σ1, ∃ l, NoDup l ∧
        (∀ e2 σ2 efs, head_step e1 σ1 e2 σ2 efs → In (e2, σ2, efs) l ∧
         \big[Rplus/0%R]_(t <- l) (head_step_prob e1 σ1 (fst (fst t)) (snd (fst t)) (snd t)) = 1%R))
  →
  ∀ e1 σ1, ∃ l, NoDup l ∧
        (∀ e2 σ2 efs, head_step e1 σ1 e2 σ2 efs ↔ In (e2, σ2, efs) l) ∧
        (l ≠ nil →
         \big[Rplus/0%R]_(t <- l) (head_step_prob e1 σ1 (fst (fst t)) (snd (fst t)) (snd t)) = 1%R).
Proof.
  intros Halt e1 σ1.
  destruct (ClassicalEpsilon.excluded_middle_informative (∃ e2 σ2 efs,
                                                             head_step e1 σ1 e2 σ2 efs))
    as [(e2&σ2&efs&Hstep)|Hnostep].
  - specialize (Halt e1 σ1). destruct Halt as (l&NoDup&Hlspec); eauto.
    set (f := λ esl,(*  match esl with *)
                 (* | (e2, σ2, efs) =>  *)
              ClassicalEpsilon.excluded_middle_informative (head_step e1 σ1
                                   (fst (fst esl)) (snd (fst esl)) (snd esl))).
    exists (filter f l).
    split_and!; auto.
    * by apply NoDup_filter.
    * intros. split.
      ** intros Hstep'. rewrite -elem_of_list_In.
         rewrite elem_of_list_filter; split.
         *** rewrite /f. destruct ClassicalEpsilon.excluded_middle_informative as [?|n]; auto.
             rewrite //= in n *.
         *** rewrite elem_of_list_In. apply Hlspec; eauto.
      ** rewrite -elem_of_list_In elem_of_list_filter. rewrite /f.
         destruct ClassicalEpsilon.excluded_middle_informative as [h|n].
         rewrite //=; auto.
         intros (?&?) => //=.
    * intros. rewrite filter_ssr_filter big_filter. 
      rewrite (@big_mkcond R R0 Rplus_monoid _ l (λ x, is_left (f x))
                              (λ i, head_step_prob e1 σ1 ((i.1).1) ((i.1).2) (i.2))).
      edestruct Hlspec as (Hin&<-); eauto. 
      rewrite //=. eapply eq_bigr => i ?.
      destruct (f i) as [?|n] => //=.
      edestruct (head_step_nonneg); eauto.
      exfalso. apply n.
      by apply head_step_strict_gt.
  - exists []. split_and!; auto.
    * econstructor.
    * split; intros HP.
      ** exfalso. apply Hnostep; eauto.
      ** inversion HP.
    * congruence.
Qed.

Section ectxi_language.
  Context {Λ : ectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
    head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.

  Definition fill (K : ectx) (e : expr Λ) : expr Λ := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  (* When something does a step, and another decomposition of the same expression
  has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
  other words, [e] also contains the reducible expression *)
  Lemma step_by_val_prefix K K' e1 e1' σ1 e2 σ2 efs :
    fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 efs →
    exists K'', K' = K'' ++ K. (* K `prefix_of` K' *)
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { clear. intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { clear -fill_val. intros K e. rewrite !eq_None_not_Some. eauto. }
    - intros Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
  Qed.

  Lemma step_by_val_eq K K' e1 e1' σ1 e2 e2' σ2 σ2' efs efs' :
    fill K e1 = fill K' e1' → head_step e1 σ1 e2 σ2 efs → head_step e1' σ1 e2' σ2' efs' →
    K = K'. 
  Proof.
    intros Hfill Hstep1 Hstep2.
    edestruct (step_by_val_prefix K K' e1 e1') as (Kl&HeqKl); eauto.
    { eapply ectxi_language_mixin; eauto. }
    edestruct (step_by_val_prefix K' K e1' e1) as (Kl'&HeqKl'); eauto.
    { eapply ectxi_language_mixin; eauto. }
    rewrite HeqKl in HeqKl'.
    apply (f_equal length) in HeqKl'.
    rewrite ?app_length in HeqKl'.
    destruct (Kl); rewrite //= in HeqKl HeqKl'; auto; try omega.
  Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill head_step head_step_prob.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    unshelve (econstructor). 
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - by intros [] [].
    - apply step_by_val_prefix.
    - apply step_by_val_eq.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
  Qed.

  Canonical Structure ectxi_lang_ectx := EctxLanguage ectxi_lang_ectx_mixin.
  Canonical Structure ectxi_prob_lang := ProbLanguageOfEctx ectxi_lang_ectx.
  Canonical Structure ectxi_lang := LanguageOfProb ectxi_prob_lang.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Instance ectxi_lang_ctx_item Ki :
    LanguageCtx (fill_item Ki).
  Proof. change (LanguageCtx (fill (Ki :: nil))). apply _. Qed.

  Global Instance ectxi_lang_ctx_prob_item Ki :
    ProbLanguageCtx (fill_item Ki).
  Proof. change (ProbLanguageCtx (fill (Ki :: nil))). apply _. Qed.
End ectxi_language.

Arguments fill {_} _ _%E.
Arguments ectxi_lang_ectx : clear implicits.
Arguments ectxi_prob_lang: clear implicits.
Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang_ectx : ectxiLanguage >-> ectxLanguage.
Coercion ectxi_prob_lang : ectxiLanguage >-> probLanguage.
Coercion ectxi_lang : ectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage :=
  let '@EctxiLanguage E V C St of_val to_val fill head head_prob mix := Λ in
  @EctxLanguage E V (list C) St of_val to_val _ _ _ _ _
    (@ectxi_lang_ectx_mixin (@EctxiLanguage E V C St of_val to_val fill head head_prob mix)).
