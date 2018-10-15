Require Import Reals.
From iris.base_logic Require Export gen_heap.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.program_logic Require Export weakestpre lifting prob_lifting.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export lang zset.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".
Import uPred.

From discprob.basic Require Import monad.
From discprob.idxval Require Import pival pival_dist pidist_singleton idist_pidist_pair ival_dist irrel_equiv ival_pair.

(** Basic rules for language operations. *)

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ
}.

Instance heapG_stateG `{heapG Σ} : stateG' heap_prob_lang Σ := {
  stateG_interp := gen_heap_ctx;
}.

Global Opaque iris_invG.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : uPred_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (atomic _ _) => solve_atomic.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

Local Hint Constructors head_step.
Local Hint Resolve alloc_fresh.
Local Hint Resolve to_of_val.

Section lifting.
Context `{heapG Σ} `{probG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Bind. This bundles some arguments that wp_ectx_bind leaves as indices. *)
Lemma wp_bind {s E e} K Φ :
  WP e @ s; E {{ v, WP fill K (of_val v) @ s; E {{ Φ }} }} ⊢ WP fill K e @ s; E {{ Φ }}.
Proof. apply: wp_prob_ectx_bind. Qed.
    
Lemma wp_bindi {s E e} Ki Φ :
  WP e @ s; E {{ v, WP fill_item Ki (of_val v) @ s; E {{ Φ }} }} ⊢
     WP fill_item Ki e @ s; E {{ Φ }}.
Proof. apply: wp_prob_bind. Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork s E e Φ :
  ▷ Φ (LitV LitUnit) ∗ ▷ WP e @ s; ⊤ {{ _, True }} ⊢ WP Fork e @ s; E {{ Φ }}.
Proof.
  rewrite -(wp_lift_pure_det_head_step_nocouple (Fork e) (Lit LitUnit) [e]); [ | eauto |].
  - by rewrite -step_fupd_intro // later_sep -(wp_value _ _ _ (Lit _)) //= right_id. 
  - intros; inv_head_step; eauto.
Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  unfold IntoVal, AsVal in *; subst;
  repeat match goal with H : is_Some _ |- _ => destruct H as [??] end;
  apply det_head_step_pure_exec; [ solve_exec_safe | solve_exec_puredet ].

Class AsRec (e : expr) (f x : binder) (erec : expr) :=
  as_rec : e = Rec f x erec.
Global Instance AsRec_rec f x e : AsRec (Rec f x e) f x e := eq_refl.
Global Instance AsRec_rec_locked_val v f x e :
  AsRec (of_val v) f x e → AsRec (of_val (locked v)) f x e.
Proof. by unlock. Qed.

Global Instance pure_rec f x (erec e1 e2 : expr)
    `{!AsVal e2, AsRec e1 f x erec, Closed (f :b: x :b: []) erec} :
  PureExec True (App e1 e2) (subst' x e2 (subst' f e1 erec)).
Proof. unfold AsRec in *; solve_pure_exec. Qed.

Global Instance pure_unop op e v v' `{!IntoVal e v} :
  PureExec (un_op_eval op v = Some v') (UnOp op e) (of_val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op e1 e2 v1 v2 v' `{!IntoVal e1 v1, !IntoVal e2 v2} :
  PureExec (bin_op_eval op v1 v2 = Some v') (BinOp op e1 e2) (of_val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_if_true e1 e2 :
  PureExec True (If (Lit (LitBool true)) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 :
  PureExec True (If (Lit (LitBool false)) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst e1 e2 v1 `{!IntoVal e1 v1, !AsVal e2} :
  PureExec True (Fst (Pair e1 e2)) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_snd e1 e2 v2 `{!AsVal e1, !IntoVal e2 v2} :
  PureExec True (Snd (Pair e1 e2)) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjL e0) e1 e2) (App e1 e0).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr e0 v e1 e2 `{!IntoVal e0 v} :
  PureExec True (Case (InjR e0) e1 e2) (App e2 e0).
Proof. solve_pure_exec. Qed.

(** Heap *)
Lemma wp_alloc s E e v :
  IntoVal e v →
  {{{ True }}} Alloc e (Lit $ LitInt 0) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  set (l := Pos.succ (fold_left Pos.max (elements (dom (gset loc) σ1)) 1%positive)).
  specialize (gen_heap_alloc σ1 l) => Hgen.
  iMod (Hgen with "Hσ") as "[Hσ Hl]".
  { rewrite /l/loc.
    match goal with
    | [ H: ∀ l', _ → σ1 !! l' = None |- _] => eapply H
    end.
    zify; split; rewrite /loc; omega.
  }
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.
    
Lemma wp_alloc_blk' s E e v k :
  0 <= k →
  IntoVal e v →
  {{{ True }}} Alloc e (Lit $ LitInt k)  @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ set] z ∈ Pset_inclusive_range l (Z.to_nat k), z ↦ v }}}.
Proof.
  iIntros (Hle <-%of_to_val Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  set (l := Pos.succ (fold_left Pos.max (elements (dom (gset loc) σ1)) 1%positive)).
  revert Hrange. rewrite Z_to_nat_to_pos.
  rewrite Z2Nat.inj_succ //=.
  rewrite -/l; generalize l; clear l.
  intros l Hrange.
  iSpecialize ("HΦ" $! l).
  iInduction (Z.to_nat size) as [|n] "IH" forall (l σ1 Hrange).
  - rewrite //=.
    specialize (gen_heap_alloc σ1 l) => Hgen.
    iMod (Hgen with "Hσ") as "[Hσ Hl]".
    { eapply Hrange. zify; split; rewrite /loc; omega. }
    iModIntro; iSplit=> //. iFrame. iApply "HΦ".
    rewrite big_opS_singleton //=.
  - specialize (gen_heap_alloc σ1 (l + Pos.of_succ_nat n)%positive v) => Hgen.
    iMod (Hgen with "Hσ") as "[Hσ Hl]".
    {
      eapply Hrange. zify; split; rewrite /loc; try omega.
      specialize (Zsucc_Pos_succ' n); zify. omega.
    }
    iPoseProof ("IH" $! l with "[] [Hl HΦ] Hσ") as "Hfin".
    { iPureIntro => l' Hrange'.
      rewrite lookup_insert_ne.
      * eapply Hrange. specialize (Pos_of_nat_le (S n)) => ?. zify. split; auto; try omega.
      * rewrite /loc. rewrite //= in Hrange'. rewrite Pos.of_nat_succ.
        zify; omega.
    }
    { iIntros "Hset". iApply "HΦ". 
      rewrite //= big_opS_union.
      * rewrite big_opS_singleton //=; iFrame.  
      * apply Pset_inclusive_disjoint_last.
    }
    rewrite //= set_block_comm //=.
Qed.

      
Lemma wp_alloc_blk s E e v k :
  IntoVal e v →
  {{{ True }}} Alloc e (Lit $ LitInt k)  @ s; E
  {{{ l, RET LitV (LitLoc l); [∗ set] z ∈ Pset_inclusive_range l (Z.to_nat k), z ↦ v }}}.
Proof.
  destruct (Z_le_dec 0 k).
  { eapply wp_alloc_blk'; auto. }
  iIntros (<-%of_to_val Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  set (l := Pos.succ (fold_left Pos.max (elements (dom (gset loc) σ1)) 1%positive)).
  specialize (gen_heap_alloc σ1 l) => Hgen.
  iMod (Hgen with "Hσ") as "[Hσ Hl]".
  { rewrite /l/loc.
    match goal with
    | [ H: ∀ l', _ → σ1 !! l' = None |- _] => eapply H
    end.
    zify; split; rewrite /loc; omega.
  }
  iModIntro; iSplit=> //.
  assert (Z.to_nat size = O) as ->.
  { apply Z_to_nat_nonpos. omega. }
  iFrame. iApply "HΦ".
  rewrite big_opS_singleton //=.
Qed.

Lemma wp_load s E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Lit (LitLoc l)) @ s; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' e v :
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Store (Lit (LitLoc l)) e @ s; E {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Lemma wp_cas_fail s E l q v' e1 v1 e2 :
  IntoVal e1 v1 → AsVal e2 → v' ≠ v1 →
  {{{ ▷ l ↦{q} v' }}} CAS (Lit (LitLoc l)) e1 e2 @ s; E
  {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (<-%of_to_val [v2 <-%of_to_val] ? Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E l e1 v1 e2 v2 :
  IntoVal e1 v1 → IntoVal e2 v2 →
  {{{ ▷ l ↦ v1 }}} CAS (Lit (LitLoc l)) e1 e2 @ s; E
  {{{ RET LitV (LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (<-%of_to_val <-%of_to_val Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

Lemma wp_faa s E l i1 e2 i2 :
  IntoVal e2 (LitV (LitInt i2)) →
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Lit (LitLoc l)) e2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (<-%of_to_val Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. by iApply "HΦ".
Qed.

(** Proof rules for derived constructs *)
Lemma wp_seq E e1 e2 Φ :
  is_Some (to_val e1) → Closed [] e2 →
  ▷ WP e2 @ E {{ Φ }} ⊢ WP Seq e1 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?). rewrite -wp_pure_step_later; by eauto. Qed.

Lemma wp_skip E Φ : ▷ Φ (LitV LitUnit) ⊢ WP Skip @ E {{ Φ }}.
Proof. rewrite -wp_seq; last eauto. by rewrite -wp_value. Qed.

Lemma wp_match_inl E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x1 :b: []) e1 →
  ▷ WP subst' x1 e0 e1 @ E {{ Φ }} ⊢ WP Match (InjL e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?) "?". rewrite -!wp_pure_step_later; by eauto. Qed.

Lemma wp_match_inr E e0 x1 e1 x2 e2 Φ :
  is_Some (to_val e0) → Closed (x2 :b: []) e2 →
  ▷ WP subst' x2 e0 e2 @ E {{ Φ }} ⊢ WP Match (InjR e0) x1 e1 x2 e2 @ E {{ Φ }}.
Proof. iIntros ([? ?] ?) "?". rewrite -!wp_pure_step_later; by eauto. Qed.

    

Lemma aux_interp_unfold (c: aux_state) :
  aux_interp c = own probG_name (● (Excl' (c : discreteC prob_state))).
Proof. done. Qed.

Lemma eq_ivd_bin_op op e1 e2 v1 v2 σ1 I:
  to_val e1 = Some v1 →
  to_val e2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some I →
  eq_ivd (ivdist_prim_step (ProbBinOp op e1 e2) σ1)
         (x ← `I; mret (prim_res_step (of_val x) σ1 [])).
Proof.
  intros Hv1 Hv2 Heval.
  symmetry.

  assert (head_reducible (ProbBinOp op e1 e2) σ1) as Hhead.
  { 
    exists (of_val (proj1_sig (ival_dist.ivd_isupport_inhabited (proj1_sig I)))).
    do 2 eexists. econstructor; eauto.
  }


  apply ival.eq_ival_primitive_fmap_bij; auto.
  - destruct I; auto.
  - apply ivdist_prim_step_primitive.
  - intros v Hin.
    edestruct (@ivdist_step_idx heap_ectxi_lang) as (i&?&Hval); last first.
    { exists i; split; eauto. }
    rewrite //=. apply head_prim_step => //=.
    set (v' := exist (λ x, ival.In_isupport x (`I)) v Hin).
    replace v with (proj1_sig v'); auto.
    eapply ProbBinOpS; eauto.
  - intros. apply of_val_inj; congruence.
  - intros v Hin.

    destruct v as [e s l|]; last first.
    {  exfalso. eapply ival_red_non_stuck; last eapply Hin.
       by apply head_prim_reducible.
    }

    efeed pose proof (@ival_non_stuck_red heap_ectxi_lang) as Hstep; eauto.
    { left. apply head_prim_reducible; eauto. }
    { eauto. }
    eapply head_reducible_prim_step in Hstep; last eauto. eauto.
    inversion Hstep; subst.

    match goal with [ H : ival.isupport _ |- _ ] => destruct H as (v'0&ix&?&?) end.
    repeat match goal with
             [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
             assert (v1 = v2) by congruence; subst; clear H2
           end.
    match goal with
      [ H1 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist1,
             H2 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist2 |- _] =>
      assert (Idist1 = Idist2) by congruence; subst; clear H2
    end.
    eexists; split; eauto. rewrite //=.
    econstructor; split; eauto.
  - intros i1 i2 Heq.
    erewrite ivdist_val_step; eauto; [].

    rewrite //=.
    rewrite head_reducible_prim_step_prob; eauto; last first.
    { apply ectxi_language_sub_redexes_are_values => Ki e.
      destruct Ki => //=; inversion 1; auto; subst; eauto.
    }


    rewrite //=.
    rewrite /head_step_prob //=.
    destruct ClassicalEpsilon.excluded_middle_informative as [?|Hnot]; last first.
    { destruct (ival.val_nonneg (`I) i1); auto. exfalso. eapply Hnot. 
      
      assert (ival.In_isupport (ival.ind (`I) i1) (`I)) as Hsupp.
      { eexists; split; eauto. }
      replace (ival.ind (`I) i1) with
          (proj1_sig (exist (λ x, ival.In_isupport x (`I)) (ival.ind (`I) i1) Hsupp)); last first.
      { eauto. }

      econstructor; eauto.
    }
    rewrite /eq_rec_r //=.
    destruct (ClassicalEpsilon.constructive_indefinite_description) as (I'&?).
    destruct (ClassicalEpsilon.constructive_indefinite_description) as (i'&v1'&v2'&?&?&?&Hval&?).
    f_equal.
    repeat match goal with
             [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
             assert (v1 = v2) by congruence; subst; clear H2
           end.
    match goal with
      [ H1 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist1,
             H2 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist2 |- _] =>
      assert (Idist1 = Idist2) by congruence; subst; clear H2
    end.
    f_equal. destruct I' as (?&Hprim). apply Hprim.
    rewrite to_of_val //= in Hval. congruence.
Qed.

Lemma wp_couple {X Y} E (m: pidist Y) (f: Y → pidist X)  I op e1 v1 e2 v2 R:
  to_val e1 = Some v1 →
  to_val e2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some I →
  irrel_couplingP (proj1_sig I) m R →
  {{{ ▷ ownProb (x ← m; f x) }}}
    ProbBinOp op e1 e2 @ E
  {{{ v, RET v; ∃ v', ownProb (f v') ∗ ⌜ R v v' ⌝ }}}.
Proof.
  iIntros (? ? ? HIc Φ) "Hprob HΦ".
  iApply (wp_lift_atomic_head_step_couple  (Φ := Φ) (ProbBinOp op e1 e2) m f
                                           (λ x y, match x with
                                                   | prim_res_irred => False
                                                   | prim_res_step e2 σ2 efs =>
                                                     match (to_val e2) with
                                                     | None => False
                                                     | Some v => R v y
                                                     end
                                                   end) with "[Hprob HΦ]"); eauto.
  iFrame "Hprob".
  iIntros (σ1) "Hσ1".
  iApply fupd_frame_l; iSplitR.
  { iPureIntro. inv_head_step.
    unshelve (econstructor).
    { exact (of_val (proj1_sig (ival_dist.ivd_isupport_inhabited (proj1_sig I)))).  }
    exists σ1, [].
    econstructor => //=. }
  iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
  iModIntro. iNext. 
  unshelve (iExists _).
  {
    rewrite //= in HIc.
    assert (eq_ivd (ivdist_prim_step (ProbBinOp op e1 e2) σ1)
                   (x ← `I; mret (prim_res_step (of_val x) σ1 []))) as Heq_ivd.
    { eapply eq_ivd_bin_op; eauto. }
    eapply irrel_coupling_proper.
    { symmetry; eauto.  }
    { eapply pidist_right_id. }
    eapply irrel_coupling_bind; first by done.
    intros ? ? HR.
    apply irrel_coupling_mret => //=.
    rewrite to_of_val. done.
  }
  iIntros (e2' σ2' efs y) "(Hp&Hown)". iMod "Hclose". iModIntro. 
  iDestruct "Hp" as %(?&?).
  inv_head_step; iFrame.
  iApply "HΦ"; eauto.
Qed.

Lemma wp_couple' {X Y} E (m: pidist Y) (f: Y → pidist X)  I op e1 v1 e2 v2 R:
  to_val e1 = Some v1 →
  to_val e2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some I →
  idist_pidist_couplingP (proj1_sig I) m R →
  {{{ ▷ ownProb (x ← m; f x) }}}
    ProbBinOp op e1 e2 @ E
  {{{ v, RET v; ∃ v', ownProb (f v') ∗ ⌜ R v v' ⌝ }}}.
Proof.
  intros; eapply wp_couple; eauto.
  by apply ip_irrel_coupling.
Qed.

Lemma wp_irrel E I op e1 v1 e2 v2:
  to_val e1 = Some v1 →
  to_val e2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some I →
  {{{ True }}}
    ProbBinOp op e1 e2 @ E
  {{{ v, RET v; ⌜ ival.In_isupport v (`I) ⌝ }}}.
Proof.
  intros.
  iIntros "? HΦ". iApply wp_lift_atomic_head_step_no_fork_nocouple; auto.
  iIntros (σ1) "Hσ !>". 
  iSplitL "".
  { iPureIntro. inv_head_step.
    unshelve (econstructor).
    { exact (of_val (proj1_sig (ival_dist.ivd_isupport_inhabited (proj1_sig I)))).  }
    exists σ1, [].
    econstructor => //=.
  }
  iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
  iModIntro. iSplit=>//; iFrame. iApply "HΦ".
  iPureIntro. destruct v'; auto.
Qed.

Require Import Psatz.

Lemma wp_flip {X Y} E (m: pidist Y) (f: Y → pidist X) z1 z2
      (Hpf: (0 <= IZR z1 / IZR z2 <= 1)%R) R:
  irrel_couplingP (ivdplus (IZR z1 / IZR z2) Hpf (mret true) (mret false)) m R →
  {{{ ▷ ownProb (x ← m; f x) }}}
    ProbBinOp BernOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E
  {{{ (b: bool), RET LitV (LitBool b); ∃ v', ownProb (f v') ∗ ⌜ R b v' ⌝ }}}.
Proof.
  intros Hc Φ.
  iIntros "Hown Hphi".
  iApply (wp_couple E m f _ BernOp _ _ _ _ (λ x y , match x with
                                                    | (LitV (LitBool b)) => R b y
                                                    | _ => False
                                                    end) with "[Hown]"); eauto.
  
  {
    eapply (irrel_coupling_proper (x ← ivdplus (IZR z1 / IZR z2) Hpf (mret true) (mret false);
                                    mret (LitV (LitBool x)))).
    { rewrite /eq_ivd. setoid_rewrite <-ival.ival_right_id at 2.
      eapply ival_coupling_eq.
      eapply ival_coupling_bind with (P := λ x y,
                                           match y with
                                       | (LitV (LitBool b)) => b = x
                                       | _ => False
                                           end).
      * rewrite //=.
        rewrite Rabs_right; last by nra.
        rewrite Rmin_left; last by nra.
        eapply ival_coupling_plus'; apply ival_coupling_mret; auto.
      * intros x' [] => //=.
        destruct l => //=. intros; subst.
        apply ival_coupling_refl.
    }
    apply pidist_right_id.
    eapply irrel_coupling_bind; first by eauto.
    intros x' y' HR.
    apply irrel_coupling_mret. auto.
  }
  iNext. iIntros (v) "Hv". iDestruct "Hv" as (v') "(Hown&%)".
  destruct v => //=.
  destruct l => //=.
  iApply "Hphi". eauto.
Qed.

Lemma wp_irrel_flip E z1 z2 (Hpf: (0 <= IZR z1 / IZR z2 <= 1)%R):
  {{{ True }}}
    ProbBinOp BernOp (Lit $ LitInt z1) (Lit $ LitInt z2) @ E
  {{{ b, RET (LitV (LitBool b)); ⌜ ((IZR z1 / IZR z2)%R = R1 → b = true) ∧
                                  ((IZR z1 / IZR z2)%R = R0 → b = false) ⌝ }}}.
Proof.
  intros.
  iIntros "_ HΦ".
  iApply wp_irrel; eauto.
  iNext. iIntros (v) "H".
  iDestruct "H" as %H'.
  rewrite //= in H'.
  destruct H' as (i&Hind&Hval).
  rewrite //= in Hind Hval.
  destruct i => //=; subst; iApply "HΦ"; iPureIntro; split; auto.
  - intros Hzero. rewrite Hzero //= Rabs_R0 Rmin_left in Hval; last nra.
    rewrite Rabs_R0 in Hval; nra.
  - intros Hone. rewrite Hone //= Rabs_R1 Rmin_left in Hval; last nra.
    replace (1 - 1)%R with R0 in Hval; auto; last by nra.
    rewrite Rabs_R0 in Hval; nra.
Qed.
  
End lifting.
