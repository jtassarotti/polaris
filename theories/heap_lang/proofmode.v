From iris.program_logic Require Export weakestpre prob_lifting.
From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Export tactics lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{heapG Σ} `{probG Σ} Δ s E Φ e e' :
  e = e' →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Ltac wp_expr_eval t :=
  try iStartProof;
  try (eapply tac_wp_expr_eval; [t; reflexivity|]).

Ltac wp_expr_simpl := wp_expr_eval simpl.
Ltac wp_expr_simpl_subst := wp_expr_eval simpl_subst.

Lemma tac_wp_pure `{heapG Σ} `{probG Σ} Δ Δ' s E e1 e2 φ Φ :
  PureExec φ e1 e2 →
  φ →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_entails Δ' (WP e2 @ s; E {{ Φ }}) →
  envs_entails Δ (WP e1 @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -wp_pure_step_later //.
Qed.

Lemma tac_wp_value `{heapG Σ} `{probG Σ} Δ s E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. rewrite /envs_entails=> ? ->. by apply wp_value. Qed.

Ltac wp_value_head := eapply tac_wp_value; [apply _|lazy beta].

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (fill K e'));
      [apply _                        (* PureExec *)
      |try fast_done                  (* The pure condition for PureExec *)
      |apply _                        (* IntoLaters *)
      |wp_expr_simpl_subst; try wp_value_head (* new goal *)
      ])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (Lit (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (Lit (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_let.

Lemma tac_wp_bind `{heapG Σ} `{probG Σ} K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (of_val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite /envs_entails=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|lazy beta]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

(** Heap tactics *)
Section heap.
Context `{heapG Σ} `{probG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

Lemma tac_wp_alloc Δ Δ' s E j K e v Φ :
  IntoVal e v →
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Lit (LitLoc l)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc e (Lit $ LitInt 0)) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_alloc_blk Δ Δ' s E j K e v k Φ :
  IntoVal e v →
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
        envs_app false (Esnoc Enil j ([∗ set] z ∈ Pset_inclusive_range l (Z.to_nat k), z ↦ v)%I)
                 Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Lit (LitLoc l)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc e (Lit $ LitInt k)) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?? HΔ.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc_blk.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_load Δ Δ' s E i K l q v Φ :
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K (of_val v) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (Lit (LitLoc l))) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ???.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' s E i K l v e v' Φ :
  IntoVal e v' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Lit LitUnit) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (Lit (LitLoc l)) e) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?????.
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' s E i K l q v e1 v1 e2 Φ :
  IntoVal e1 v1 → AsVal e2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I → v ≠ v1 →
  envs_entails Δ' (WP fill K (Lit (LitBool false)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ??????.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' s E i K l v e1 v1 e2 v2 Φ :
  IntoVal e1 v1 → IntoVal e2 v2 →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I → v = v1 →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Lit (LitBool true)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (Lit (LitLoc l)) e1 e2) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ???????; subst.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_cas_suc.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_faa Δ Δ' Δ'' s E i K l i1 e2 i2 Φ :
  IntoVal e2 (LitV (LitInt i2)) →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV (LitInt i1))%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (i1 + i2)))) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (Lit (LitInt i1)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (FAA (Lit (LitLoc l)) e2) @ s; E {{ Φ }}).
Proof.
  rewrite /envs_entails=> ?????; subst.
  rewrite -wp_bind. eapply wand_apply; first exact: (wp_faa _ _ _ i1 _ i2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  iPoseProofCore lem as false true (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; iApplyHyp H; try iNext; wp_expr_simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_alloc _ _ _ _ H K); [apply _|..])
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [apply _
    |first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |wp_expr_simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_alloc_blk" ident(l) "as" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_alloc_blk _ _ _ _ H K); [apply _|..])
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [apply _
    |first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |wp_expr_simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc_blk" ident(l) :=
  let H := iFresh in wp_alloc_blk l as H.

Tactic Notation "wp_load" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_store _ _ _ _ _ _ K); [apply _|..])
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_store: cannot find" l "↦ ?"
    |env_cbv; reflexivity
    |wp_expr_simpl; try first [wp_pure (Seq (Lit LitUnit) _)|wp_value_head]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_fail _ _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?"
    |try congruence
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_suc _ _ _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?"
    |try congruence
    |env_cbv; reflexivity
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.

Tactic Notation "wp_faa" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_faa _ _ _ _ _ _ K); [apply _|..])
      |fail 1 "wp_faa: cannot find 'CAS' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?"
    |env_cbv; reflexivity
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_faa: not a 'wp'"
  end.

Require Import Reals Psatz.
From discprob.basic Require Import monad.
From discprob.idxval Require Import pival pival_dist pidist_singleton
     idist_pidist_pair ival_dist irrel_equiv ival_pair irrel_equiv.

Lemma tac_wp_flip {X Y} `{heapG Σ} `{probG Σ} m (f: Y → pidist X) R Δ Δ' E i K z1 z2 Φ
  (Hpf: (0 <= IZR z1 / IZR z2 <= 1)%R):
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, ownProb (x ← m; f x))%I →
  irrel_couplingP (ivdplus (IZR z1 / IZR z2) Hpf (mret true)
                           (mret false))
                  m R →
  (∀ b y, R b y → ∃ Δ'',
        envs_simple_replace i false
                            (Esnoc Enil i (ownProb (f y))) Δ'
        = Some Δ'' ∧
      envs_entails Δ'' (WP fill K (Lit $ LitBool b) @ E {{ Φ }})) →
  envs_entails Δ (WP fill K (ProbBinOp BernOp (Lit $ LitInt z1) (Lit $ LitInt z2)) @ E {{ Φ }}).
Proof.
  intros ?? HIc HΔ''. rewrite -wp_bind. eapply wand_apply.
  eapply wp_flip; eauto.
  rewrite into_laterN_env_sound -later_sep envs_lookup_sound //; simpl.
  iIntros "(Hp&Hdel)".
  iNext. iFrame. iIntros (v) "Hown".
  iDestruct "Hown" as (v') "(Hown&%)".
  edestruct (HΔ'') as (Δ''&?&HΔ''_entails); eauto.
  iApply into_ih_entails; eauto.
  iPoseProof (envs_simple_replace_sound' with "[Hdel]") as "H"; eauto.
  iApply "H". rewrite //=. iFrame.
Qed.

Lemma tac_wp_flip' {X Y} `{heapG Σ} `{probG Σ} m (f: Y → pidist X) R Δ Δ' E i K z1 z2 Φ
  (Hpf: (0 <= IZR z1 / IZR z2 <= 1)%R):
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, ownProb (x ← m; f x))%I →
  idist_pidist_couplingP (ivdplus (IZR z1 / IZR z2) Hpf (mret true) (mret false))
                  m R →
  (∀ b y, R b y → ∃ Δ'',
        envs_simple_replace i false
                            (Esnoc Enil i (ownProb (f y))) Δ'
        = Some Δ'' ∧
      envs_entails Δ'' (WP fill K (Lit $ LitBool b) @ E {{ Φ }})) →
  envs_entails Δ (WP fill K (ProbBinOp BernOp (Lit $ LitInt z1) (Lit $ LitInt z2)) @ E {{ Φ }}).
Proof.
  intros; eapply tac_wp_flip; eauto. eapply ip_irrel_coupling; eauto.
Qed.

Lemma tac_wp_irrel_flip `{heapG Σ} `{probG Σ} Δ Δ' E j K z1 z2 Φ
  (Hpf: (0 <= IZR z1 / IZR z2 <= 1)%R):
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ b, ∃ Δ'',
        envs_app false (Esnoc Enil j (⌜ ((IZR z1 / IZR z2)%R = R1 → b = true) ∧
                                        ((IZR z1 / IZR z2)%R = R0 → b = false)⌝)) Δ' = Some Δ'' ∧
        envs_entails Δ'' (WP fill K (Lit (LitBool b)) @ E {{ Φ }})) →
  envs_entails Δ (WP fill K (ProbBinOp BernOp (Lit $ LitInt z1) (Lit $ LitInt z2)) @ E {{ Φ }}).
Proof.
  intros ? HΔ. rewrite -wp_bind. eapply wand_apply; first exact: wp_irrel_flip.
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.
  

Require Import Psatz. 
Tactic Notation "wp_flip"  open_constr(m) open_constr(R) ident(b) ident(y) ident(HR) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_flip m _ R _ _ _ _ K); [apply _|..])
      |fail 1 "wp_flip: cannot find 'flip' in" e];
    [ iAssumptionCore | (* try (abstract nra) | *) |
      intros b y HR; eexists; split;
      [ env_cbv; try reflexivity | simpl; try wp_value_head (* new goal *)]]
    (* [apply _ ] *)
    (* |first [intros l | fail 1 "wp_flip:" (* l "not fresh" *) ];
      eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |simpl; try wp_value_head]] *)
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_flip_irrel" ident(b) "as" constr(H) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp _ ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_irrel_flip _ _ _ H K) ; [|..])
      |fail 1 "wp_flip: cannot find 'flip' in" e];
      [ | apply _ |
        intros b; eexists; split;
        [env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
        |simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

(*
Module tests.
From iris.heap_lang Require Import notation. 
Section foo.
  Context `{heapG Σ} `{probG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition heap_faa : expr :=
    let: "l" := Alloc #0 (#1 + #1) in
    let: "x" := FAA "l" #1 in
    "x".

  Lemma heap_faa_spec :
    WP heap_faa {{ v, ⌜ v = LitV $ LitInt 0 ⌝ }}%I.
  Proof.
    iIntros. rewrite /heap_faa.
    wp_op. wp_alloc_blk l as "Hl".
    wp_let.

    wp_faa.
    wp_let. done.
  Qed.

  Definition heap_e2 : expr :=
    let: "x" := flip (#1) (#2) in
    let: "y" := flip (#1) (#2) in
    "x" = "y".


  
  Program Definition flip_half := pidist_plus (1/2)%R _ (mret true) (mret false).
  Next Obligation.
    nra.
  Qed.


From iris.algebra Require Import gmap auth agree gset coPset.

  Lemma heap_e2_irrel E :
    True ⊢ WP heap_e2 @ E {{ v, ∃ v', ⌜ v = LitV $ LitBool v' ⌝ }}%I.
  Proof.
    iIntros "Hprob". rewrite /heap_e2.
    rewrite /flip_half.
    wp_flip_irrel b as "H".
  Abort.
End foo.
End tests.
*)
