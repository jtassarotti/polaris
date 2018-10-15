From iris.algebra Require Export ofe.
Set Default Proof Using "Type".

Section language_mixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → expr → state → list expr → Prop).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → expr → state → list expr → Prop;
  language_mixin : LanguageMixin of_val to_val prim_step
}.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Arguments Language {_ _ _ _ _ _} _.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments prim_step {_} _ _ _ _ _.

Canonical Structure stateC Λ := leibnizC (state Λ).
Canonical Structure valC Λ := leibnizC (val Λ).
Canonical Structure exprC Λ := leibnizC (expr Λ).

Definition cfg (Λ : language) := (list (expr Λ) * state Λ)%type.

Class LanguageCtx {Λ : language} (K : expr Λ → expr Λ) := {
  fill_not_val e :
    to_val e = None → to_val (K e) = None;
  fill_step e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    prim_step (K e1) σ1 (K e2) σ2 efs;
  fill_step_inv e1' σ1 e2 σ2 efs :
    to_val e1' = None → prim_step (K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 e2' σ2 efs;
  fill_inj : Inj (=) (=) K;
}.

Instance language_ctx_id Λ : LanguageCtx (@id (expr Λ)).
Proof. constructor; try naive_solver. intros ???; auto. Qed.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None.
  Proof. apply language_mixin. Qed.

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, prim_step e σ e' σ' efs.
  Definition irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬prim_step e σ e' σ' efs.
  Definition stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible e σ.

  (* [Atomic WeaklyAtomic]: This (weak) form of atomicity is enough to open
     invariants when WP ensures safety, i.e., programs never can get stuck.  We
     have an example in lambdaRust of an expression that is atomic in this
     sense, but not in the stronger sense defined below, and we have to be able
     to open invariants around that expression.  See `CasStuckS` in
     [lambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/blob/master/theories/lang/lang.v).

     [Atomic StronglyAtomic]: To open invariants with a WP that does not ensure
     safety, we need a stronger form of atomicity.  With the above definition,
     in case `e` reduces to a stuck non-value, there is no proof that the
     invariants have been established again. *)
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' σ' efs :
      prim_step e σ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Inductive step (ρ1 ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
       prim_step e1 σ1 e2 σ2 efs →
       step ρ1 ρ2.

  Inductive istep (i: nat) (ρ1 ρ2 : cfg Λ) : Prop :=
    | istep_atomic e1 σ1 e2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
       prim_step e1 σ1 e2 σ2 efs →
       length t1 = i →
       istep i ρ1 ρ2.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ.
  Proof. intros [??] ??? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma reducible_fill `{LanguageCtx Λ K} e σ :
    to_val e = None → reducible (K e) σ → reducible e σ.
  Proof.
    intros ? (e'&σ'&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill `{LanguageCtx Λ K} e σ :
    to_val e = None → irreducible e σ → irreducible (K e) σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma step_Permutation (t1 t1' t2 : list (expr Λ)) σ1 σ2 :
    t1 ≡ₚ t1' → step (t1,σ1) (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ step (t1',σ1) (t2',σ2).
  Proof.
    intros Ht [e1 σ1' e2 σ2' efs tl tr ?? Hstep]; simplify_eq/=.
    move: Ht; rewrite -Permutation_middle (symmetry_iff (≡ₚ)).
    intros (tl'&tr'&->&Ht)%Permutation_cons_inv.
    exists (tl' ++ e2 :: tr' ++ efs); split; [|by econstructor].
    by rewrite -!Permutation_middle !assoc_L Ht.
  Qed.

  Class PureExec (P : Prop) (e1 e2 : expr Λ) := {
    pure_exec_safe σ :
      P → reducible e1 σ;
    pure_exec_puredet σ1 e2' σ2 efs :
      P → prim_step e1 σ1 e2' σ2 efs → σ1 = σ2 ∧ e2 = e2' ∧ efs = [];
  }.

  Lemma hoist_pred_pure_exec (P : Prop) (e1 e2 : expr Λ) :
    (P → PureExec True e1 e2) →
    PureExec P e1 e2.
  Proof. intros HPE. split; intros; eapply HPE; eauto. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K `{LanguageCtx Λ K} e1 e2 φ :
    PureExec φ e1 e2 →
    PureExec φ (K e1) (K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *. naive_solver eauto using fill_step.
    - intros σ1 e2' σ2 efs ? Hpstep.
      destruct (fill_step_inv e1 σ1 e2' σ2 efs) as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1) as (? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 e2'' σ2 efs) as (-> & -> & ->); auto.
  Qed.

  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : to_val e = Some v.

  Class AsVal (e : expr Λ) := as_val : is_Some (to_val e).
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /= to_of_val; eauto.
  Qed.
End language.
