From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From stdpp Require Export collections gmap mapset.
Set Default Proof Using "Type".

(* The union CMRA *)
Section gset.
  Context `{Countable K}.
  Implicit Types X Y : gset K.

  Canonical Structure gsetC := discreteC (gset K).

  Instance gset_valid : Valid (gset K) := λ _, True.
  Instance gset_unit : Unit (gset K) := (∅ : gset K).
  Instance gset_op : Op (gset K) := union.
  Instance gset_pcore : PCore (gset K) := λ X, Some X.

  Lemma gset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma gset_core_self X : core X = X.
  Proof. done. Qed.
  Lemma gset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->]. rewrite gset_op_union. set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L. by exists Z.
  Qed.

  Lemma gset_ra_mixin : RAMixin (gset K).
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !gset_op_union assoc_L.
    - intros X1 X2. by rewrite !gset_op_union comm_L.
    - intros X. by rewrite gset_core_self idemp_L.
  Qed.
  Canonical Structure gsetR := discreteR (gset K) gset_ra_mixin.

  Global Instance gset_cmra_discrete : CmraDiscrete gsetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gset_ucmra_mixin : UcmraMixin (gset K).
  Proof. split. done. intros X. by rewrite gset_op_union left_id_L. done. Qed.
  Canonical Structure gsetUR := UcmraT (gset K) gset_ucmra_mixin.

  Lemma gset_opM X mY : X ⋅? mY = X ∪ from_option id ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma gset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma gset_local_update X Y X' : X ⊆ X' → (X,Y) ~l~> (X',X').
  Proof.
    intros (Z&->&?)%subseteq_disjoint_union_L.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite gset_op_union. set_solver.
  Qed.

  Global Instance gset_core_id X : CoreId X.
  Proof. by apply core_id_total; rewrite gset_core_self. Qed.
End gset.

Arguments gsetC _ {_ _}.
Arguments gsetR _ {_ _}.
Arguments gsetUR _ {_ _}.

(* The disjoint union CMRA *)
Inductive gset_disj K `{Countable K} :=
  | GSet : gset K → gset_disj K
  | GSetBot : gset_disj K.
Arguments GSet {_ _ _} _.
Arguments GSetBot {_ _ _}.

Section gset_disj.
  Context `{Countable K}.
  Arguments op _ _ !_ !_ /.
  Arguments cmra_op _ !_ !_ /.
  Arguments ucmra_op _ !_ !_ /.

  Canonical Structure gset_disjC := leibnizC (gset_disj K).

  Instance gset_disj_valid : Valid (gset_disj K) := λ X,
    match X with GSet _ => True | GSetBot => False end.
  Instance gset_disj_unit : Unit (gset_disj K) := GSet ∅.
  Instance gset_disj_op : Op (gset_disj K) := λ X Y,
    match X, Y with
    | GSet X, GSet Y => if decide (X ## Y) then GSet (X ∪ Y) else GSetBot
    | _, _ => GSetBot
    end.
  Instance gset_disj_pcore : PCore (gset_disj K) := λ _, Some ε.

  Ltac gset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal GSet)|done|exfalso]; set_solver by eauto.

  Lemma gset_disj_included X Y : GSet X ≼ GSet Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (GSet Z). gset_disj_solve.
  Qed.
  Lemma gset_disj_valid_inv_l X Y : ✓ (GSet X ⋅ Y) → ∃ Y', Y = GSet Y' ∧ X ## Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma gset_disj_union X Y : X ## Y → GSet X ⋅ GSet Y = GSet (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma gset_disj_valid_op X Y : ✓ (GSet X ⋅ GSet Y) ↔ X ## Y.
  Proof. simpl. case_decide; by split. Qed.

  Lemma gset_disj_ra_mixin : RAMixin (gset_disj K).
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; gset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
    - intros [X|]; gset_disj_solve.
    - exists (GSet ∅); gset_disj_solve.
    - intros [X1|] [X2|]; gset_disj_solve.
  Qed.
  Canonical Structure gset_disjR := discreteR (gset_disj K) gset_disj_ra_mixin.

  Global Instance gset_disj_cmra_discrete : CmraDiscrete gset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma gset_disj_ucmra_mixin : UcmraMixin (gset_disj K).
  Proof. split; try apply _ || done. intros [X|]; gset_disj_solve. Qed.
  Canonical Structure gset_disjUR := UcmraT (gset_disj K) gset_disj_ucmra_mixin.

  Arguments op _ _ _ _ : simpl never.

  Lemma gset_disj_alloc_updateP_strong P (Q : gset_disj K → Prop) X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    (∀ i, i ∉ X → P i → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
  Proof.
    intros Hfresh HQ.
    apply cmra_discrete_updateP=> ? /gset_disj_valid_inv_l [Y [->?]].
    destruct (Hfresh (X ∪ Y)) as (i&?&?); first set_solver.
    exists (GSet ({[ i ]} ∪ X)); split.
    - apply HQ; set_solver by eauto.
    - apply gset_disj_valid_op. set_solver by eauto.
  Qed.
  Lemma gset_disj_alloc_updateP_strong' P X :
    (∀ Y, X ⊆ Y → ∃ j, j ∉ Y ∧ P j) →
    GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X ∧ P i.
  Proof. eauto using gset_disj_alloc_updateP_strong. Qed.

  Lemma gset_disj_alloc_empty_updateP_strong P (Q : gset_disj K → Prop) :
    (∀ Y : gset K, ∃ j, j ∉ Y ∧ P j) →
    (∀ i, P i → Q (GSet {[i]})) → GSet ∅ ~~>: Q.
  Proof.
    intros. apply (gset_disj_alloc_updateP_strong P); eauto.
    intros i; rewrite right_id_L; auto.
  Qed.
  Lemma gset_disj_alloc_empty_updateP_strong' P :
    (∀ Y : gset K, ∃ j, j ∉ Y ∧ P j) →
    GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]} ∧ P i.
  Proof. eauto using gset_disj_alloc_empty_updateP_strong. Qed.

  Section fresh_updates.
    Local Set Default Proof Using "Type*".
    Context `{Fresh K (gset K), !FreshSpec K (gset K)}.

    Lemma gset_disj_alloc_updateP (Q : gset_disj K → Prop) X :
      (∀ i, i ∉ X → Q (GSet ({[i]} ∪ X))) → GSet X ~~>: Q.
    Proof.
      intro; eapply gset_disj_alloc_updateP_strong with (λ _, True); eauto.
      intros Y ?; exists (fresh Y); eauto using is_fresh.
    Qed.
    Lemma gset_disj_alloc_updateP' X :
      GSet X ~~>: λ Y, ∃ i, Y = GSet ({[ i ]} ∪ X) ∧ i ∉ X.
    Proof. eauto using gset_disj_alloc_updateP. Qed.

    Lemma gset_disj_alloc_empty_updateP (Q : gset_disj K → Prop) :
      (∀ i, Q (GSet {[i]})) → GSet ∅ ~~>: Q.
    Proof.
      intro. apply gset_disj_alloc_updateP. intros i; rewrite right_id_L; auto.
    Qed.
    Lemma gset_disj_alloc_empty_updateP' : GSet ∅ ~~>: λ Y, ∃ i, Y = GSet {[ i ]}.
    Proof. eauto using gset_disj_alloc_empty_updateP. Qed.
  End fresh_updates.

  Lemma gset_disj_dealloc_local_update X Y :
    (GSet X, GSet Y) ~l~> (GSet (X ∖ Y), GSet ∅).
  Proof.
    apply local_update_total_valid=> _ _ /gset_disj_included HYX.
    rewrite local_update_unital_discrete=> -[Xf|] _ /leibniz_equiv_iff //=.
    rewrite {1}/op /=. destruct (decide _) as [HXf|]; [intros[= ->]|done].
    by rewrite difference_union_distr_l_L
      difference_diag_L !left_id_L difference_disjoint_L.
  Qed.
  Lemma gset_disj_dealloc_empty_local_update X Z :
    (GSet Z ⋅ GSet X, GSet Z) ~l~> (GSet X, GSet ∅).
  Proof.
    apply local_update_total_valid=> /gset_disj_valid_op HZX _ _.
    assert (X = (Z ∪ X) ∖ Z) as HX by set_solver.
    rewrite gset_disj_union // {2}HX. apply gset_disj_dealloc_local_update.
  Qed.
  Lemma gset_disj_dealloc_op_local_update X Y Z :
    (GSet Z ⋅ GSet X, GSet Z ⋅ GSet Y) ~l~> (GSet X,GSet Y).
  Proof.
    rewrite -{2}(left_id ε _ (GSet Y)).
    apply op_local_update_frame, gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma gset_disj_alloc_op_local_update X Y Z :
    Z ## X → (GSet X,GSet Y) ~l~> (GSet Z ⋅ GSet X, GSet Z ⋅ GSet Y).
  Proof.
    intros. apply op_local_update_discrete. by rewrite gset_disj_valid_op.
  Qed.
  Lemma gset_disj_alloc_local_update X Y Z :
    Z ## X → (GSet X,GSet Y) ~l~> (GSet (Z ∪ X), GSet (Z ∪ Y)).
  Proof.
    intros. apply local_update_total_valid=> _ _ /gset_disj_included ?.
    rewrite -!gset_disj_union //; last set_solver.
    auto using gset_disj_alloc_op_local_update.
  Qed.
  Lemma gset_disj_alloc_empty_local_update X Z :
    Z ## X → (GSet X, GSet ∅) ~l~> (GSet (Z ∪ X), GSet Z).
  Proof.
    intros. rewrite -{2}(right_id_L _ union Z).
    apply gset_disj_alloc_local_update; set_solver.
  Qed.
End gset_disj.

Arguments gset_disjC _ {_ _}.
Arguments gset_disjR _ {_ _}.
Arguments gset_disjUR _ {_ _}.
