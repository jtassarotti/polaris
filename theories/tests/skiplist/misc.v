Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.

From iris.tests.skiplist Require Import code.

Import seq_ext.

Lemma NoDup_inj_in_map' {T1 T2: Type} (f: T1 → T2) (l: list T1) :
  (∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) →
  NoDup l → NoDup (map f l).
Proof.
  intros Hinj. rewrite ?NoDup_ListNoDup => ?.
  eapply seq_ext.NoDup_inj_in_map; eauto.
  { intros. eapply Hinj; eauto; apply elem_of_list_In; eauto. }
Qed.


Section gset_extra.
  Context `{Countable K}.
  Implicit Types X Y Z : gset K.
  Lemma gset_local_update_union X Y W : (X,Y) ~l~> (X ∪ W,Y ∪ W).
  Proof.
    rewrite local_update_unital_discrete=> Z' _ /leibniz_equiv_iff->.
    split. done. rewrite gset_op_union. set_solver.
  Qed.
End gset_extra.

Lemma length_remove_le {A: Type} {HEQ} (a: A) l:
  (length (remove HEQ a l) <= length l)%nat.
Proof.
  induction l => //=.
  destruct HEQ; eauto; rewrite //=; omega.
Qed.

Lemma length_remove_lt {A: Type} {HEQ} (a: A) l:
  List.In a l →
  (length (remove HEQ a l) < length l)%nat.
Proof.
  induction l.
  - inversion 1. 
  - inversion 1; subst.
    * rewrite //=. destruct HEQ; last by (exfalso; eauto).
      eapply le_lt_trans; first apply length_remove_le; eauto.
    * rewrite //=. destruct HEQ; subst.
      ** eapply le_lt_trans; first apply length_remove_le; eauto.
      ** rewrite //=. feed pose proof IHl; eauto. omega.
Qed.

Definition set_of_list {K : Type} `{EqDecision K} `{Countable K} (L: seq K) : gset K :=
   {| mapset_car := map_of_list [seq (x, ()) | x <- remove_dups L] |}.

Lemma elements_insert
      {K : Type} `{EqDecision K} `{Countable K} (np: K) (m: gmap K ()) :
  m !! np = None →
  elements (Mapset (<[np :=()]> m) : gset K) ≡ₚ np :: (elements (Mapset m)).
Proof.
  intros.
  rewrite /elements/mapset_elements//=. 
  rewrite map_to_list_insert//=. 
Qed.

Lemma elements_map_of_list {K: Type} `{EqDecision K} `{Countable K} (L: seq K) :
  NoDup L →
  L ≡ₚ elements {| mapset_car := map_of_list [seq (x, ()) | x <- L] |}.
Proof.
  intros HNoDup.
  induction L; rewrite //=.
  rewrite elements_insert.
  - econstructor. eapply IHL. inversion HNoDup; eauto.
  - apply not_elem_of_map_of_list.
    rewrite stdpp_ext.list_fmap_map //=.
    rewrite map_legacy //= map_map //=.
    rewrite List.map_id. inversion HNoDup; subst; eauto.
Qed.

Lemma elements_set_of_list {K: Type} `{EqDecision K} `{Countable K} (L: seq K) :
  ∀ x, x ∈ L ↔ x ∈ (set_of_list L).
Proof.
  intros x. rewrite /set_of_list. rewrite -elem_of_elements.
  rewrite -elements_map_of_list; last apply NoDup_remove_dups.
  rewrite elem_of_remove_dups //=.
Qed.
  
Lemma Sorted_Zlt_hd_nin (x: Z) (L: list Z):
  Sorted Z.lt (x :: L) → x ∉ L.
Proof.
  induction L => Hsort.
  eauto with *.
  apply not_elem_of_cons; split.
  * apply Sorted_inv in Hsort as (?&Hhd).
    inversion Hhd; subst; omega.
  * eapply IHL.
    apply Sorted_inv in Hsort as (Hsort&Hhd).
    apply Sorted_inv in Hsort as (?&Hhd').
    apply Sorted_cons; eauto.
    inversion Hhd'. subst.
    ** econstructor. 
    ** econstructor. inversion Hhd. omega.
Qed.

Lemma Sorted_Zlt_NoDup (L: list Z):
  Sorted Z.lt L → NoDup L.
Proof.
  induction L as [|a L] => Hsorted.
  - econstructor.
  - specialize (Sorted_Zlt_hd_nin a L Hsorted); auto.
    apply Sorted_inv in Hsorted as (Hsorted&?).
    econstructor; eauto.
Qed.

Lemma Sorted_Zle_NoDup_Zlt (L: list Z):
  Sorted Z.le L → NoDup L → Sorted Z.lt L.
Proof.
  intros Hs Hn. revert Hs.
  induction Hn; first auto. 
  intros. apply Sorted_inv in Hs as (Hs'&Hhd).
  econstructor.
  * eauto.
  * inversion Hhd.
    ** subst. econstructor.
    ** subst. econstructor.
       assert (x ≠ b).
       { firstorder. }
       omega.
Qed.

Lemma Sorted_Zge_NoDup_Zgt (L: list Z):
  Sorted Z.ge L → NoDup L → Sorted Z.gt L.
Proof.
  intros Hs Hn. revert Hs.
  induction Hn; first auto. 
  intros. apply Sorted_inv in Hs as (Hs'&Hhd).
  econstructor.
  * eauto.
  * inversion Hhd.
    ** subst. econstructor.
    ** subst. econstructor.
       assert (x ≠ b).
       { firstorder. }
       omega.
Qed.

From discprob.idxval Require Import pival
     pival_dist ival_dist irrel_equiv idist_pidist_pair pidist_pair extrema pidist_post_cond.

From Coq Require Export Sorting.Mergesort.

Module ZOrder <: Orders.TotalLeBool.
  Definition t := Z.
  Definition leb (x y: t) : bool.
    destruct (Z_le_dec x y).
    - exact true. 
    - exact false.
  Defined.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros a1 a2. rewrite /leb.
    do 2 destruct (Z_le_dec); auto; try omega.
  Qed.
End ZOrder.

Module ZOrderGe <: Orders.TotalLeBool.
  Definition t := Z.
  Definition leb (x y: t) : bool.
    destruct (Z_ge_dec x y).
    - exact true. 
    - exact false.
  Defined.
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros a1 a2. rewrite /leb.
    do 2 destruct (Z_ge_dec); auto; try omega.
  Qed.
End ZOrderGe.

Module Export ZSort := Sorting.Mergesort.Sort ZOrder.
Module ZSortGe := Sorting.Mergesort.Sort ZOrderGe.

Lemma Sorted_Zorder_Zle l:
  Sorted ZOrder.leb l → Sorted Zle l.
Proof.
  induction 1 as [| ?? Hsorted IH Hhd].
  - econstructor.
  - econstructor; eauto.
    inversion Hhd as [| ? ? Hhd'].
    * subst. econstructor.
    * subst. econstructor. 
      rewrite /ZOrder.leb in Hhd'. destruct Z_le_dec; eauto.
      exfalso; eauto.
Qed.

Lemma Sorted_ZorderGe_Zge l:
  Sorted ZOrderGe.leb l → Sorted Zge l.
Proof.
  induction 1 as [| ?? Hsorted IH Hhd].
  - econstructor.
  - econstructor; eauto.
    inversion Hhd as [| ? ? Hhd'].
    * subst. econstructor.
    * subst. econstructor. 
      rewrite /ZOrderGe.leb in Hhd'. destruct Z_ge_dec; eauto.
      exfalso; eauto.
Qed.

Lemma Sorted_Zle_uniq l l':
  Sorted Zle l →
  Sorted Zle l' →
  Permutation l l' → l = l'.
Proof.
  revert l'.
  induction l.
  - intros l' ?? ?%Permutation.Permutation_nil. subst. auto.
  - intros l' Hsorted Hsorted' Hperm.
    destruct l' as [| a' l'].
    { symmetry in Hperm. apply Permutation.Permutation_nil in Hperm. congruence. } 
    cut (a = a').
    { intros; subst.  f_equal.
      eapply IHl.
      { eapply Sorted_inv; eauto. }
      { eapply Sorted_inv; eauto. }
      apply Permutation.Permutation_cons_inv in Hperm; eauto.
    }
    apply Zle_antisym.
    * apply Sorted_StronglySorted in Hsorted; last eauto with *.
      inversion Hsorted as [| ??? Hall]; subst.
      assert (List.In a' (a :: l)) as [|]; subst.
      { apply elem_of_list_In. rewrite Hperm. by left. }
      ** reflexivity. 
      ** eapply List.Forall_forall in Hall; eauto.
    * apply Sorted_StronglySorted in Hsorted'; last eauto with *.
      inversion Hsorted' as [| ??? Hall]; subst.
      assert (List.In a (a' :: l')) as [|]; subst.
      { apply elem_of_list_In. rewrite -Hperm. by left. }
      ** reflexivity. 
      ** eapply List.Forall_forall in Hall; eauto.
Qed.

Lemma Sorted_nodekey_uniq l l':
  Sorted Zlt (map node_key l) →
  Sorted Zlt (map node_key l') →
  Permutation l l' →
  l = l'.
Proof.
  revert l'.
  induction l.
  - intros l' ?? ?%Permutation.Permutation_nil. subst. auto.
  - intros l' Hsorted Hsorted' Hperm.
    destruct l' as [| a' l'].
    { symmetry in Hperm. apply Permutation.Permutation_nil in Hperm. congruence. } 
    destruct_decide (decide (a = a')) as Hcase.
    { intros; subst.  f_equal.
      eapply IHl.
      { eapply Sorted_inv; eauto. }
      { eapply Sorted_inv; eauto. }
      apply Permutation.Permutation_cons_inv in Hperm; eauto.
    }
    
    exfalso. cut (node_key a < node_key a' ∧ node_key a' < node_key a); first omega.
    split.
    * apply Sorted_StronglySorted in Hsorted; last eauto with *.
      inversion Hsorted as [| ??? Hall]; subst.
      assert (List.In a' (a :: l)) as [|]; subst.
      { apply elem_of_list_In. rewrite Hperm. by left. }
      ** congruence. 
      ** eapply List.Forall_forall in Hall; eauto.
         apply in_map_iff; eexists; eauto.
    * apply Sorted_StronglySorted in Hsorted'; last eauto with *.
      inversion Hsorted' as [| ??? Hall]; subst.
      assert (List.In a (a' :: l')) as [|]; subst.
      { apply elem_of_list_In. rewrite -Hperm. by left. }
      ** congruence. 
      ** eapply List.Forall_forall in Hall; eauto.
         apply in_map_iff; eexists; eauto.
Qed.

Lemma Sorted_sort_folded tl:
  Sorted ZOrder.leb (sort tl).
Proof.
  feed pose proof (LocallySorted_sort tl) as Htl.
  rewrite //=/ZOrder.leb in Htl *.
  induction Htl; econstructor; eauto.
  inversion H; subst; econstructor.
  destruct Z_le_dec; eauto.
Qed.

Lemma Sorted_sort_ge_folded tl:
  Sorted ZOrderGe.leb (ZSortGe.sort tl).
Proof.
  feed pose proof (ZSortGe.LocallySorted_sort tl) as Htl.
  rewrite //=/ZOrderGe.leb in Htl *.
  induction Htl; econstructor; eauto.
  inversion H; subst; econstructor.
  destruct Z_ge_dec; eauto.
Qed.

Lemma remove_perm_proper {A: Type} HEQ (x: A) l1 l2:
  Permutation l1 l2 →
  Permutation (remove HEQ x l1) (remove HEQ x l2).
Proof.
  induction 1.
  - eauto.
  - rewrite //=. destruct HEQ; eauto.
  - rewrite //=. repeat destruct HEQ; eauto.
    econstructor.
  - etransitivity; eauto.
Qed.
 
Lemma remove_not_in a l:
  ¬ (a ∈ l) →
  remove Z_eq_dec a l = l.
Proof.
  intros Hnin. induction l => //=.
  destruct Z_eq_dec.
  { exfalso.  eapply Hnin. subst. left. }
  f_equal. eapply IHl. set_solver.
Qed.


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
Lemma rep_to_node_inj np np':
  rep_to_node np = rep_to_node np' →
  np = np'.
Proof.
  destruct np as (((?&?)&?)&?). 
  destruct np' as (((?&?)&?)&?). 
  rewrite /rep_to_node/node_val/node_key/node_lock/node_next//=. inversion 1. congruence.
Qed.

Import List seq.

Lemma Sorted_lt_hd L np_left np
  (Hin : In np (np_left :: L))
  (Hsorted : Sorted Z.lt [seq node_key i | i <- np_left :: L]):
  np = np_left ∨ node_key np_left < node_key np.
Proof.
  apply Sorted_StronglySorted in Hsorted; last first.
  { eauto with *. }
  rewrite map_cons in Hsorted.
  apply StronglySorted_inv in Hsorted as (?&Hforall).
  destruct Hin; first by left.
  right.
  rewrite List.Forall_forall in Hforall * => Hforall.
  eapply Hforall. apply in_map. eauto.
Qed.
      
Lemma app_cat {A: Type} (l1 l2: list A):
  cat l1 l2 = app l1 l2.
Proof. rewrite //=. Qed.

Lemma StronglySorted_app {A: Type} R (L1 L2: list A):
  StronglySorted R (L1 ++ L2) →
  StronglySorted R L1 ∧ StronglySorted R L2.
Proof.
  induction L1.
  - rewrite //=; intros; intuition; econstructor.
  - intros Hs.
    inversion Hs; subst; eauto.
    edestruct IHL1; eauto. split; auto.
    econstructor; eauto.
    apply list.Forall_forall. intros. eapply list.Forall_forall; eauto.
    apply elem_of_list_In. apply in_or_app. left. apply elem_of_list_In; done.
Qed.

Lemma Sorted_Zlt_app (L1 L2: list Z):
  Sorted Zlt (L1 ++ L2) → Sorted Zlt L1 ∧ Sorted Zlt L2.
Proof.
  intros HS. apply Sorted_StronglySorted in HS; last eauto with *.
  apply StronglySorted_app in HS as (?&?); split; eauto using StronglySorted_Sorted.
Qed.

Lemma Sorted_nodekey_snoc np' L np'':
  Sorted Z.lt [seq node_key i | i <- np' :: L ++ [:: np'']] →
  Sorted Z.lt [seq node_key i | i <- np' :: L].
Proof.
  rewrite -cat_cons map_cat.
  intros Hsorted. eapply Sorted_Zlt_app in Hsorted; intuition.
Qed.

Lemma Sorted_nodekey_snoc' L np'':
  Sorted Z.lt [seq node_key i | i <- L ++ [:: np'']] →
  Sorted Z.lt [seq node_key i | i <- L].
Proof.
  rewrite map_cat.
  intros Hsorted. eapply Sorted_Zlt_app in Hsorted; intuition.
Qed.

Definition Zbetween z1 z2 x:
  { z1 < x < z2} + {¬ z1 < x < z2}.
Proof.
  destruct (Z_lt_dec z1 x); last first.
  { right. omega. }
  destruct (Z_lt_dec x z2); last first.
  { right. omega. }
  left. auto.
Qed.

Definition list_between (L: list Z) z1 z2 :=
  filter (λ x, if (Zbetween z1 z2 x) then true else false) L.

Lemma NoDup_pred_unique {A: Type} (L1 L2 L1' L2': list A) np pred1 pred2:
  NoDup (L1 ++ pred1 :: np :: L2) →
  L1 ++ pred1 :: np :: L2 = L1' ++ pred2 :: np :: L2' →
  pred1 = pred2.
Proof.
  revert L2 L1' L2'.
  induction L1 => //=.
  - intros L2 L1' L2' Hno_dup Heq.
    destruct L1' as [| a L1'].
    * rewrite //= in Heq; congruence. 
    * destruct L1' as [| b L1'].
      ** rewrite //= in Heq. assert (L2 = np :: L2') by congruence.
         subst. exfalso.
         rewrite ?NoDup_cons_iff in Hno_dup *.
         intros (Hnin1&Hnin2&?&?).
         apply Hnin2. by left.
      ** rewrite //= in Heq. assert (L2 = L1' ++ (pred2 :: np :: L2')) by congruence.
         subst. 
         rewrite ?NoDup_cons_iff in Hno_dup *.
         intros (Hnin1&Hnin2&?).
         exfalso. apply Hnin2.
         apply in_or_app. right. econstructor; econstructor. auto.
  - intros L2 L1' L2' Hnd.
    destruct L1' as [| a' L1'].
    { rewrite //=.
      rewrite -NoDup_ListNoDup in Hnd *.
      rewrite -cat_cons.
      rewrite app_cat NoDup_app. intros (Hnd1&Hnd2&Hnd3) Heq.
      cut (np = pred1 ∨ In np L1).
      { intros [Heqpred1|Hin].
        * exfalso.  subst.
          rewrite NoDup_ListNoDup in Hnd3 *. inversion 1 as [|? Heq1 Hnin ?]; subst.
          eapply Hnin. by left.
        * exfalso.  eapply Hnd2. right; apply elem_of_list_In; eauto. right. by left.
      }
      destruct L1.
      * rewrite //= in Heq. inversion Heq; subst; auto.
      * right. inversion Heq; subst. by left.
    }
    inversion 1; subst. eapply IHL1; eauto.
    inversion Hnd; eauto.
Qed.

Lemma list_between_all_gt l z1 z2:
  (∀ i, In i l → i > z2) →
  list_between l z1 z2 = [::].
Proof.
  induction l as [|a l] => Hrange //=.
  - intros.  destruct Zbetween => //=.
    * feed pose proof (Hrange a); first by left.
      omega.
    * eapply IHl. intros. eapply Hrange. by right.
Qed.

Lemma list_between_all_ge l z1 z2:
  (∀ i, In i l → i >= z2) →
  list_between l z1 z2 = [::].
Proof.
  induction l as [|a l] => Hrange //=.
  - intros.  destruct Zbetween => //=.
    * assert (a >= z2); first apply Hrange; eauto.
      { by left. }
      omega.
    * eapply IHl. intros. eapply Hrange. by right.
Qed.

Lemma list_between_cat z1 z2 l1 l2:
  list_between (l1 ++ l2) z1 z2 = list_between l1 z1 z2 ++ list_between l2 z1 z2.
Proof.
  rewrite /list_between. rewrite filter_cat //=.
Qed.

Lemma list_between_all_le_ge l z1 z2:
  (∀ i, In i l → i <= z1 ∨ i >= z2) →
  list_between l z1 z2 = [::].
Proof.
  induction l as [|a l] => Hrange //=.
  - intros.  destruct Zbetween => //=.
    * assert (a <= z1 ∨ a >= z2); first apply Hrange; eauto.
      { by left. }
      omega.
    * eapply IHl. intros. eapply Hrange. by right.
Qed.

Lemma list_between_all_in_range l z1 z2:
  (∀ i, In i l → z1 < i < z2) →
  list_between l z1 z2 = l.
Proof.
  induction l as [|a l] => Hrange //=.
  - intros.  destruct Zbetween => //=.
    * f_equal. eapply IHl. intros; eapply Hrange; by right.
    * destruct (Hrange a); first by left.
      exfalso. omega.
Qed.

Lemma Zlt_Sorted_forall_before z L1 L2:
  Sorted Zlt (L1 ++ [:: z & L2]) →
  ∀ i, In i L1 → i < z.
Proof.
  induction L1 => //=.
  intros Hsorted i [Heq_hd|Hin]; last first.
  { eapply IHL1; auto. apply Sorted_inv in Hsorted; intuition. }
  subst. apply Sorted_StronglySorted in Hsorted; last eauto with *.
  apply StronglySorted_inv in Hsorted as (?&Hhd).
  eapply Forall_forall; eauto.
  apply in_app_iff. right; left. done.
Qed.

Lemma list_between_perm L1 L2 k1 k2:
  Permutation L1 L2 →
  Permutation (list_between L1 k1 k2) (list_between L2 k1 k2).
Proof.
  induction 1.
  * rewrite //=. 
  * rewrite //=. 
    repeat destruct Zbetween; eauto.
  * rewrite //=. 
    repeat destruct Zbetween; econstructor; eauto.
  * etransitivity; eauto.
Qed.

Global Instance list_between_perm_Proper:
  Proper (Permutation ==> eq ==> eq ==> Permutation) list_between.
Proof.
  intros ?? Hperm ?? -> ?? ->.
  apply list_between_perm; eauto.
Qed.

Global Instance fold_left_perm_Proper:
  Proper (Permutation ==> eq ==> eq) (fold_left Zmax).
Proof.
  intros L1 L2 Hperm ?? ->.
  apply Zle_antisym.
  * apply fold_left_Zle_max_lub.
    { intros r' Hin. apply seq_ext.fold_left_Zmax_ub.
      apply elem_of_list_In. rewrite -Hperm. apply elem_of_list_In.
      auto. }
    apply seq_ext.fold_left_Zmax_init.
  * apply seq_ext.fold_left_Zle_max_lub.
    { intros r' Hin. apply seq_ext.fold_left_Zmax_ub.
      apply elem_of_list_In. rewrite Hperm. apply elem_of_list_In.
      auto. }
    apply seq_ext.fold_left_Zmax_init.
Qed.


Lemma fold_left_Sorted_Zmax hd L1 max L2:
  Sorted Z.lt (hd :: L1 ++ [:: max & L2]) →
  fold_left Z.max (L1 ++ [:: max]) hd = max.
Proof.
  revert hd.
  induction L1 => hd //=.
  - intros (?&Hd)%Sorted_inv.
    rewrite Z.max_r; auto. inversion Hd; subst; eauto. omega.
  - intros Hsort. rewrite -{2}(IHL1 a).
    * f_equal. rewrite Z.max_r; auto.
      apply Sorted_inv in Hsort as (?&Hd).
      inversion Hd; subst; eauto. omega.
    * apply Sorted_inv in Hsort; intuition.
Qed.

Lemma Sorted_Zlt_cover_gap L1 L2 zpred zfind k:
  Sorted Zlt (L1 ++ (zpred :: zfind :: L2)) →
  zpred < k →
  zfind >= k →
  In k (L1 ++ (zpred :: zfind :: L2)) →
  zfind = k.
Proof.
  induction L1.
  - rewrite //= => Hsort Hr1 Hr2 Hin. inversion Hin as [|[Heq|Hin']]; subst; try omega.
    exfalso. apply Sorted_StronglySorted in Hsort; last eauto with *.
    apply StronglySorted_inv in Hsort as (Hsort&_).
    apply StronglySorted_inv in Hsort as (Hsort&hd).
    assert (zfind < k); last by omega.
    eapply Forall_forall; eauto.
  - rewrite //=. intros Hsort ?? Hin.
    inversion Hin.
    * subst.
      exfalso. apply Sorted_StronglySorted in Hsort; last eauto with *.
      apply StronglySorted_inv in Hsort as (Hsort&Hhd).
      assert (k < zpred); last by omega.
      eapply Forall_forall; eauto.
      apply in_app_iff. right. by left.
    * eapply IHL1; eauto.
      apply Sorted_inv in Hsort; intuition.
Qed.

Definition key_equiv (S: gset node_rep) (S_keys: gset Z) :=
  Permutation (elements S_keys) (map node_key (elements S)).

Lemma key_equiv_in np S Skeys:
  key_equiv S Skeys →
  np ∈ S →
  node_key np ∈ Skeys.
Proof.
  rewrite /key_equiv.
  intros Hperm ?%elem_of_elements.
  apply elem_of_elements. rewrite Hperm.
  apply elem_of_list_In.
  apply in_map, elem_of_list_In; auto.
Qed.

Lemma key_equiv_nin np S Skeys:
  key_equiv S Skeys →
  ¬ node_key np ∈ Skeys →
  ¬ np ∈ S.
Proof.
  intros ? Hnin Hin. eapply Hnin, key_equiv_in; eauto.
Qed.
