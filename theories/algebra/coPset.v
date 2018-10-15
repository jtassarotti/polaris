From iris.algebra Require Export cmra.
From iris.algebra Require Import updates local_updates.
From stdpp Require Export collections coPset.
Set Default Proof Using "Type".
(** This is pretty much the same as algebra/gset, but I was not able to
generalize the construction without breaking canonical structures. *)

(* The union CMRA *)
Section coPset.
  Implicit Types X Y : coPset.

  Canonical Structure coPsetC := discreteC coPset.

  Instance coPset_valid : Valid coPset := λ _, True.
  Instance coPset_unit : Unit coPset := (∅ : coPset).
  Instance coPset_op : Op coPset := union.
  Instance coPset_pcore : PCore coPset := Some.

  Lemma coPset_op_union X Y : X ⋅ Y = X ∪ Y.
  Proof. done. Qed.
  Lemma coPset_core_self X : core X = X.
  Proof. done. Qed.
  Lemma coPset_included X Y : X ≼ Y ↔ X ⊆ Y.
  Proof.
    split.
    - intros [Z ->]. rewrite coPset_op_union. set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L. by exists Z.
  Qed.

  Lemma coPset_ra_mixin : RAMixin coPset.
  Proof.
    apply ra_total_mixin; eauto.
    - solve_proper.
    - solve_proper.
    - solve_proper.
    - intros X1 X2 X3. by rewrite !coPset_op_union assoc_L.
    - intros X1 X2. by rewrite !coPset_op_union comm_L.
    - intros X. by rewrite coPset_core_self idemp_L.
  Qed.
  Canonical Structure coPsetR := discreteR coPset coPset_ra_mixin.

  Global Instance coPset_cmra_discrete : CmraDiscrete coPsetR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coPset_ucmra_mixin : UcmraMixin coPset.
  Proof. split. done. intros X. by rewrite coPset_op_union left_id_L. done. Qed.
  Canonical Structure coPsetUR := UcmraT coPset coPset_ucmra_mixin.

  Lemma coPset_opM X mY : X ⋅? mY = X ∪ from_option id ∅ mY.
  Proof. destruct mY; by rewrite /= ?right_id_L. Qed.

  Lemma coPset_update X Y : X ~~> Y.
  Proof. done. Qed.

  Lemma coPset_local_update X Y X' : X ⊆ X' → (X,Y) ~l~> (X',X').
  Proof.
    intros (Z&->&?)%subseteq_disjoint_union_L.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite coPset_op_union. set_solver.
  Qed.
End coPset.

(* The disjoiny union CMRA *)
Inductive coPset_disj :=
  | CoPset : coPset → coPset_disj
  | CoPsetBot : coPset_disj.

Section coPset_disj.
  Arguments op _ _ !_ !_ /.
  Canonical Structure coPset_disjC := leibnizC coPset_disj.

  Instance coPset_disj_valid : Valid coPset_disj := λ X,
    match X with CoPset _ => True | CoPsetBot => False end.
  Instance coPset_disj_unit : Unit coPset_disj := CoPset ∅.
  Instance coPset_disj_op : Op coPset_disj := λ X Y,
    match X, Y with
    | CoPset X, CoPset Y => if decide (X ## Y) then CoPset (X ∪ Y) else CoPsetBot
    | _, _ => CoPsetBot
    end.
  Instance coPset_disj_pcore : PCore coPset_disj := λ _, Some ε.

  Ltac coPset_disj_solve :=
    repeat (simpl || case_decide);
    first [apply (f_equal CoPset)|done|exfalso]; set_solver by eauto.

  Lemma coPset_disj_included X Y : CoPset X ≼ CoPset Y ↔ X ⊆ Y.
  Proof.
    split.
    - move=> [[Z|]]; simpl; try case_decide; set_solver.
    - intros (Z&->&?)%subseteq_disjoint_union_L.
      exists (CoPset Z). coPset_disj_solve.
  Qed.
  Lemma coPset_disj_valid_inv_l X Y :
    ✓ (CoPset X ⋅ Y) → ∃ Y', Y = CoPset Y' ∧ X ## Y'.
  Proof. destruct Y; repeat (simpl || case_decide); by eauto. Qed.
  Lemma coPset_disj_union X Y : X ## Y → CoPset X ⋅ CoPset Y = CoPset (X ∪ Y).
  Proof. intros. by rewrite /= decide_True. Qed.
  Lemma coPset_disj_valid_op X Y : ✓ (CoPset X ⋅ CoPset Y) ↔ X ## Y.
  Proof. simpl. case_decide; by split. Qed.

  Lemma coPset_disj_ra_mixin : RAMixin coPset_disj.
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|]; destruct 1; coPset_disj_solve.
    - by constructor.
    - by destruct 1.
    - intros [X1|] [X2|] [X3|]; coPset_disj_solve.
    - intros [X1|] [X2|]; coPset_disj_solve.
    - intros [X|]; coPset_disj_solve.
    - exists (CoPset ∅); coPset_disj_solve.
    - intros [X1|] [X2|]; coPset_disj_solve.
  Qed.
  Canonical Structure coPset_disjR := discreteR coPset_disj coPset_disj_ra_mixin.

  Global Instance coPset_disj_cmra_discrete : CmraDiscrete coPset_disjR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma coPset_disj_ucmra_mixin : UcmraMixin coPset_disj.
  Proof. split; try apply _ || done. intros [X|]; coPset_disj_solve. Qed.
  Canonical Structure coPset_disjUR := UcmraT coPset_disj coPset_disj_ucmra_mixin.
End coPset_disj.
