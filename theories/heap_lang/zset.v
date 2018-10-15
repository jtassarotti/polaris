Require Import Reals.
From iris.base_logic Require Export gen_heap.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.program_logic Require Export weakestpre lifting prob_lifting.
From iris.program_logic Require Import ectx_lifting.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import tactics.
From iris.proofmode Require Import tactics.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".
Import uPred.


Fixpoint Zset_inclusive_range (z: Z) (gap : nat) : gset Z :=
  match gap with
  | O => {[ z ]}
  | S n' => {[ z + S n']} ∪ (Zset_inclusive_range z n')
  end.

Definition Zset_exclusive_range (z: Z) (gap: nat) : gset Z :=
  Zset_inclusive_range z gap ∖  {[ z; z + gap ]}.

Lemma Zset_inclusive_range_spec z gap:
  ∀ z', z' ∈ (Zset_inclusive_range z gap) ↔ (z <= z' <= z + gap).
Proof.
  induction gap.
  - rewrite //= => z'. split.
    * intros ?%elem_of_singleton. subst. omega.
    * intros (?&?); assert (z = z') as -> by omega. set_solver.
  - rewrite /Zset_inclusive_range -/Zset_inclusive_range => z'. split.
    * intros [Hspz%elem_of_singleton|Hrec]%elem_of_union.
      ** split; omega.
      ** destruct (IHgap z') as (Himpl&?). specialize (Himpl Hrec). destruct Himpl; split; try omega.
         etransitivity; first eassumption.
         rewrite Nat2Z.inj_succ.
         omega.
    * intros (?&Hle).
      apply Zle_lt_or_eq in Hle as [Hlt|?].
      ** apply elem_of_union_r. eapply IHgap; eauto.
         rewrite Nat2Z.inj_succ in Hlt *.
         omega.
      ** apply elem_of_union_l. set_solver.
Qed.

Lemma Zset_exclusive_range_spec z gap:
  ∀ z', z' ∈ (Zset_exclusive_range z gap) ↔ (z < z' < z + gap).
Proof.
  intros z'. split.
  - rewrite /Zset_exclusive_range. 
    intros (Hincl&Hneq)%elem_of_difference.
    apply Zset_inclusive_range_spec in Hincl.
    assert (z' ≠ z ∧ z' ≠ z + gap) by set_solver.
    omega.
  - rewrite /Zset_exclusive_range. 
    intros (?&?).
    apply elem_of_difference; split.
    * apply Zset_inclusive_range_spec; omega.
    * assert (z' ≠ z ∧ z' ≠ z + gap) by omega.
      set_solver.
Qed.

Definition Zlt_range (z1 z2: Z) : gset Z := Zset_exclusive_range z1 (Z.to_nat (z2 - z1)).

Lemma Zlt_range_spec z1 z2:
  ∀ z', z' ∈ (Zlt_range z1 z2) ↔ (z1 < z' < z2).
Proof.
  intros z'.
  rewrite /Zlt_range Zset_exclusive_range_spec; split.
  - intros (?&Hup).  split; auto.
    replace z2 with (z1 + (z2 - z1)); last by omega.
    destruct (Z_le_dec 0 (z2 - z1)).
    * rewrite Z2Nat.id in Hup; auto.
    * rewrite Z_to_nat_nonpos //= in Hup; last by omega.
      omega.
  - intros (?&?).
    rewrite Z2Nat.id; omega.
Qed.

Lemma Zlt_range_split z1 z2 z:
  z1 < z < z2 → Zlt_range z1 z2 = Zlt_range z1 z ∪ Zlt_range z z2 ∪ {[ z ]}.
Proof.
  intros Hrange.
  rewrite -leibniz_equiv_iff.
  intros x. split.
  - rewrite Zlt_range_spec. intros (?&?).
    destruct (Ztrichotomy_inf x z) as [[Hlt|Heq]|Hgt].
    * do 2 apply elem_of_union_l. rewrite Zlt_range_spec. omega.
    * apply elem_of_union_r. set_solver. 
    * apply elem_of_union_l, elem_of_union_r. rewrite Zlt_range_spec. omega.
  - rewrite Zlt_range_spec. intros [[Hin|Hin]%elem_of_union|Hin]%elem_of_union. 
    * rewrite Zlt_range_spec in Hin *; omega.
    * rewrite Zlt_range_spec in Hin *; omega.
    * apply elem_of_singleton in Hin. subst. auto.
Qed.

Lemma Zlt_range_split_op z1 z2 z:
  z1 < z < z2 → GSet (Zlt_range z1 z2) = GSet (Zlt_range z1 z) ⋅ GSet (Zlt_range z z2)
                                              ⋅ GSet ({[ z ]}).
Proof.
  intros Hrange. rewrite (Zlt_range_split z1 z2 z) //.
  rewrite ?gset_disj_union; auto.
  * intros z' [Hin%Zlt_range_spec|Hin%Zlt_range_spec]%elem_of_union.
    ** intros; cut (z' = z); first omega.
       set_solver.
    ** intros; cut (z' = z); first omega.
       set_solver.
  * intros z'. rewrite ?Zlt_range_spec. omega.
Qed.

Local Open Scope positive_scope.

Fixpoint Pset_inclusive_range (z: positive) (gap : nat) : gset positive :=
  match gap with
  | O => {[ z ]}
  | S n' => {[ z + Pos.of_succ_nat n']} ∪ (Pset_inclusive_range z n')
  end.

Definition Pset_exclusive_r_range (z: positive) (gap : nat) : gset positive :=
  Pset_inclusive_range z gap ∖ {[(Z.to_pos (Zpos z + Z.of_nat gap))]}.

Lemma Pset_inclusive_range_spec z gap:
  ∀ z', z' ∈ (Pset_inclusive_range z gap) ↔ (z <= z' < z + Pos.of_succ_nat gap).
Proof.
  induction gap.
  - rewrite //= => z'. split.
    * intros ?%elem_of_singleton. subst. zify; omega.
    * intros (?&?); assert (z = z') as -> by (zify; omega). set_solver.
  - rewrite /Pset_inclusive_range -/Pset_inclusive_range => z'. split.
    * intros [Hspz%elem_of_singleton|Hrec]%elem_of_union.
      ** split; zify; omega.
      ** destruct (IHgap z') as (Himpl&?). specialize (Himpl Hrec). destruct Himpl; split; try (zify; omega).
    * intros (?&Hle).
      assert (z' < z + Pos.of_succ_nat gap ∨ z' = z + Pos.of_succ_nat gap) as [Hlt|?].
      { zify. omega. }
      ** apply elem_of_union_r. eapply IHgap; eauto.
      ** apply elem_of_union_l. set_solver.
Qed.

Lemma Pset_inclusive_disjoint_last l n:
  {[(l + Pos.of_succ_nat n)%positive]} ## Pset_inclusive_range l n.
Proof.
  intros z. rewrite Pset_inclusive_range_spec.
  intros ->%elem_of_singleton. zify. omega.
Qed.

Lemma Z_to_nat_to_pos z:
  Z.to_pos z = Pos.of_nat (Z.to_nat z).
Proof.
  induction z => //=.
  rewrite Z2Nat.inj_pos Pos2Nat.id //.
Qed.

Lemma Pos_of_nat_le n: (Pos.of_nat n <= Pos.of_nat (S n))%positive.
Proof.
  rewrite /Pos.of_nat; do 2 induction n => //=; zify; omega.
Qed.

Lemma Zsucc_Pos_succ (n: nat): (Z.succ n <= Z.pos (Pos.of_nat (S n)))%Z.
Proof.
  rewrite /Pos.of_nat; do 2 induction n => //=; zify; omega.
Qed.

Lemma Zsucc_Pos_succ' (n: nat): (Z.succ n < Z.pos (Pos.of_nat (S (S n))))%Z.
Proof.
  rewrite /Pos.of_nat; do 2 induction n => //=; zify; omega.
Qed.

Lemma set_block_comm v l n n' σ1:
  (Pos.of_succ_nat n <= n')%positive →
  set_block v l n (<[(l + n')%positive:=v]> σ1) =
  <[(l + n')%positive:=v]>(set_block v l n σ1).
Proof.
  revert v l n' σ1.
  induction n => v l n' σ1 Hle.
  - rewrite //=. rewrite insert_commute //=. rewrite /loc. zify; omega.
  - rewrite //= IHn //=. 
    * rewrite insert_commute //=. rewrite /loc. zify; omega.
    * zify. omega.
Qed.