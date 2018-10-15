Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset gmap agree.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.
Set Default Proof Using "Type".

From iris.tests.skiplist Require Import code misc idxval spec_raw.
From discprob.idxval Require Import pidist_post_cond pidist_fin_singleton fin_extrema.
From discprob.idxval Require Import fin_ival fin_ival_dist.



Module Skiplist_Expected (Params: SKIPLIST_PARAMS).
  Import Params.
  Module Raw_spec := Skiplist_Raw_Spec Params. 
  Import Raw_spec.


  Lemma cost_bounded1 l lt lb:
    NoDup l →
    pspec (skiplist l lt lb) (λ ls, length (fst ls) <= length l + length lt ∧
                                    length (snd ls) <= length l + length lb)%nat.
  Proof.
    intros HNoDup.
    rewrite skiplist_equiv_single; last first.
    { apply NoDup_ListNoDup; auto. }
    clear HNoDup.
    revert lt lb. induction l => lt lb.
    - rewrite //= singleton_mret. apply pspec_mret.
      rewrite //= -?Permuted_sort; split; try omega.
    - rewrite /single_skiplist -/single_skiplist singleton_bind.
      eapply pspec_mbind with (P := λ l, (length l <= length lt + 1)%nat).
      * rewrite singleton_plus ?singleton_mret.
        apply pspec_pidist_plus; apply pspec_mret; rewrite //=; omega.
      * intros lt' Hle. eapply pspec_conseq; first eapply IHl.
        intros (ls1&ls2) => //=.
        intros (?&?); split; omega.
  Qed.

  Local Open Scope nat_scope.

  Lemma cost_top_bounded_length l k:
    cost_top l k <= S (length l).
  Proof.
    induction l => //=.
    rewrite /cost_top //=.
    destruct Zbetween => //=; rewrite /cost_top in IHl; omega.
  Qed.

  Lemma cost_bottom_bounded_length lt l k:
    cost_bottom lt l k <= S (length l).
  Proof.
    induction l => //=.
    rewrite /cost_bottom //=.
    destruct Zbetween => //=; rewrite /cost_bottom in IHl; omega.
  Qed.

  Lemma cost_bounded2 l k:
    NoDup l →
    pspec (skiplist l [::] [::]) (λ ls, skip_cost (fst ls) (snd ls) k <= S (length l) + S (length l)).
  Proof.
    intros HNoDup.
    eapply pspec_conseq; first eapply cost_bounded1; eauto.
    intros (l1&l2) => //=. intros (Hle1&Hle2).
    rewrite /skip_cost/level2_cost.
    specialize (cost_top_bounded_length l1 k).
    specialize (cost_bottom_bounded_length l1 l2 k).
    destruct (decide _); omega.
  Qed.

  Import misc.
  Import monad.
  Import fin_ival_dist.

  Lemma top_remaining_large l l1 l2 k:
    (∀ x, In x l → x >= k)%Z →
    Ex_ivd (λ ls, INR (cost_top (fst ls) k)) (single_skiplist l l1 l2) = (INR (cost_top l1 k)).
  Proof.
    revert l1 l2.
    induction l => l1 l2.
    - intros. rewrite /single_skiplist/cost_top.
      rewrite {2}(Permuted_sort l1).
      apply: Ex_ival_mret.
    - intros Hin.
      rewrite /single_skiplist -/single_skiplist.
      setoid_rewrite ivd_plus_bind.
      setoid_rewrite Ex_ivd_ivdplus.
      rewrite ?ivd_left_id.
      rewrite IHl; last first.
      { intros. eapply Hin. by right. }
      rewrite IHl; last first.
      { intros. eapply Hin. by right. }
      rewrite {2}/cost_top/list_between.
      simpl filter. destruct Zbetween.
      { exfalso. cut (a >= k)%Z; first by omega.
        eapply Hin. by left.
      }
      rewrite //=/list_between//=. nra.
  Qed.
    
  Local Open Scope R.
  Lemma top_split_list l1 l2 lt lb k:
    (∀ x, In x l1 → INT_MIN < x < k)%Z →
    (∀ x, In x l2 → x >= k)%Z →
    Ex_ivd (λ ls, INR (cost_top (fst ls) k)) (single_skiplist (l1 ++ l2) lt lb)
    = (INR (cost_top lt k) + INR (length l1) / 2)%R.
  Proof.
    revert lt lb.
    induction l1 => lt lb Hle Hge.
    - rewrite top_remaining_large //=; field.
    - rewrite cat_cons. rewrite /single_skiplist -/single_skiplist.
      setoid_rewrite ivd_plus_bind.
      setoid_rewrite Ex_ivd_ivdplus.
      rewrite ?ivd_left_id.
      rewrite IHl1; last first.
      { intros. eapply Hge. auto. }
      { intros. eapply Hle. by right. }
      rewrite IHl1; last first.
      { intros. eapply Hge. auto. }
      { intros. eapply Hle. by right. }
      rewrite {2}/cost_top/list_between.
      simpl filter. destruct Zbetween; last first.
      { exfalso. cut (INT_MIN < a < k)%Z; first by omega.
        eapply Hle. by left.
      }
      rewrite /cost_top. rewrite S_INR.
      rewrite S_INR. simpl length. rewrite ?S_INR.
      rewrite //=/list_between//=. ring_simplify. nra.
  Qed.

  Lemma list_between_split l k1 k2:
    ∃ l1 l2, Permutation l (l1 ++ list_between l k1 k2 ++ l2) ∧
             (∀ x, In x l1 → x <= k1)%Z ∧ (∀ x, In x l2 → x >= k2)%Z.
  Proof.
    induction l.
    - exists [::], [::] => //=.
    - destruct IHl as (l1&l2&Hperm&Hl&Hg).
      simpl list_between. destruct Zbetween as [|Hngt].
      * exists l1, l2; split; auto.
        rewrite {1}Hperm.
        rewrite app_cat. rewrite Permutation_app_comm.
        rewrite app_comm_cons.
        rewrite Permutation_app_comm.
        rewrite app_comm_cons. done.
      * assert (a <= k1 ∨ a >= k2)%Z as [Hle|Hge] by omega.
        ** exists (a :: l1), l2.
           split_and!; eauto.
           *** rewrite {1}Hperm //=.
           *** intros ? [[]|]; eauto; try omega.
        ** exists l1, (a :: l2). 
           split_and!; eauto.
           *** rewrite {1}Hperm //=.
               rewrite app_cat. rewrite app_assoc Permutation_app_comm.
               rewrite app_comm_cons. rewrite Permutation_app_comm -app_assoc //=.
           *** intros ? [[]|]; eauto; try omega.
  Qed.

  Lemma list_between_In_inv1 l k1 k2:
    (∀ x, In x (list_between l k1 k2) → k1 < x ∧ x < k2)%Z.
  Proof.
    induction l => //=.
    intros x. destruct Zbetween; eauto.
    intros [[]|Hin]; auto.
  Qed.

  Lemma list_between_In l k1 k2:
    (∀ x, In x l → k1 < x → x < k2 → In x (list_between l k1 k2))%Z.
  Proof.
    induction l => //=.
    intros x [[]|Hin]; destruct Zbetween; eauto; intros; try omega.
    * by left.
    * right. eapply IHl; eauto.
  Qed.

  Lemma Ex_cost_top l k:
    (∀ x, In x l → INT_MIN < x < INT_MAX)%Z →
    Ex_ivd (λ ls, INR (cost_top (fst ls) k)) (single_skiplist l [::] [::])
    = 1 + INR (length (list_between l INT_MIN k)) / 2.
  Proof.
    intros Hin.
    edestruct (list_between_split l INT_MIN k) as (l1&l2&Hperm&Hl1&Hg2).
    assert (l1 = [::]).
    {  destruct l1 as [| z l1]; auto. exfalso. cut (INT_MIN < z ∧ z <= INT_MIN)%Z; first by omega.
       split.
       * eapply Hin. rewrite Hperm. apply in_app_iff.
         do 2 left => //=.
       * apply Hl1. by left.
    }
    subst. rewrite //= in Hperm. rewrite {1}Hperm.
    rewrite top_split_list //=.
    intros x Hin'. eapply list_between_In_inv1; eauto.
  Qed.

  Global Instance ret_top_perm_Proper:
    Proper (Permutation ==> eq ==> eq) ret_top.
  Proof.
    intros l1 l2 Hperm k ? <-.
    rewrite /ret_top.
    rewrite Hperm //=.
  Qed.

  Lemma cost_bottom_cons1 l1 l2 a k:
    (INT_MIN < a)%Z →
    (a >= k ∨ (∃ i', In i' l1 ∧ a <= i' < k))%Z →
    cost_bottom l1 (a :: l2) k = cost_bottom l1 l2 k.
  Proof.
    intros Hmin.
    induction l1 as [| a' l1'].
    - rewrite //=/cost_bottom. intros [Hge|Hcase].
      * simpl list_between => //=. destruct Zbetween.
        ** omega.
        ** done.
      * firstorder.
    - rewrite /cost_bottom. intros [Hge|Hcase].
      * simpl list_between => //=. destruct Zbetween.
        ** omega.
        ** done.
      * simpl list_between => //=. destruct Zbetween as [Hb|Hnb].
        ** exfalso.  destruct Hb as (Hret&?).
           destruct Hcase as (i'&Hin&?&?).
           cut (i' <= ret_top (a' :: l1') k)%Z; first by omega.
           rewrite /ret_top. 
           apply seq_ext.fold_left_Zmax_ub.
           apply list_between_In; eauto.
           omega.
        ** done.
  Qed.

  Lemma ret_top_cons1 l a k:
    (a >= k)%Z →
    ret_top (a :: l) k = ret_top l k.
  Proof.
    intros Hge.
    rewrite /ret_top. simpl list_between. destruct Zbetween; try omega.
  Qed.

  Lemma ret_top_cons2 l a k:
    (∃ i', In i' l ∧ a <= i' < k)%Z →
    ret_top (a :: l) k = ret_top l k.
  Proof.
    intros Hge.
    rewrite /ret_top. simpl list_between. destruct Hge as (i'&Hin&?&?).
    destruct Zbetween; try omega.
    apply Z.le_antisymm.
    * apply seq_ext.fold_left_Zle_max_lub. 
      ** intros r' Hin'.
         destruct Hin' as [[]|Hin'].
         *** transitivity i'; auto. apply seq_ext.fold_left_Zmax_ub.
             apply list_between_In; auto; omega.
         *** apply seq_ext.fold_left_Zmax_ub; auto.
      ** apply seq_ext.fold_left_Zmax_init.
    * apply seq_ext.fold_left_Zmax_cons.
  Qed.

  Lemma cost_bottom_cons2 l1 l2 a k:
    (INT_MIN < a)%Z →
    (a >= k ∨ (∃ i', In i' l1 ∧ a <= i' < k))%Z →
    cost_bottom (a :: l1) (a :: l2) k = cost_bottom l1 l2 k.
  Proof.
    intros Hmin.
    induction l1 as [| a' l1'].
    - rewrite //=/cost_bottom. intros [Hge|Hcase].
      * simpl list_between => //=. destruct Zbetween as [|Hnzb].
        ** omega.
        ** rewrite ret_top_cons1 //=.
      * firstorder.
    - rewrite /cost_bottom. intros [Hge|Hcase].
      * simpl list_between => //=. destruct Zbetween as [|Hnzb].
        ** omega.
        ** rewrite ret_top_cons1 //=.
      * simpl list_between => //=. destruct Zbetween as [Hb|Hnb].
        ** exfalso.  destruct Hb as (Hret&?).
           destruct Hcase as (i'&Hin&?&?).
           cut (i' <= ret_top (a :: a' :: l1') k)%Z; first by omega.
           rewrite /ret_top. 
           apply seq_ext.fold_left_Zmax_ub.
           apply list_between_In; eauto.
           *** right. done.
           *** omega.
        ** rewrite ret_top_cons2 //=.
  Qed.

  Lemma bottom_remaining_large l l1 l2 k:
    (∀ x, In x l → INT_MIN < x < INT_MAX)%Z →
    (∀ x, In x l → x >= k ∨ (∃ i', In i' l1 ∧ x <= i' < k))%Z →
    Ex_ivd (λ ls, INR (cost_bottom (fst ls) (snd ls) k))
           (single_skiplist l l1 l2) = (INR (cost_bottom l1 l2 k)).
  Proof.
    revert l1 l2.
    induction l => l1 l2.
    - intros. rewrite /single_skiplist/cost_bottom.
      rewrite {2}(Permuted_sort l1).
      rewrite {2}(Permuted_sort l2).
      apply: Ex_ival_mret.
    - intros Hin1 Hin2.
      rewrite /single_skiplist -/single_skiplist.
      setoid_rewrite ivd_plus_bind.
      setoid_rewrite Ex_ivd_ivdplus.
      rewrite ?ivd_left_id.
      rewrite IHl; last first.
      { intros. eapply Hin2. by right. }
      { intros. eapply Hin1; by right. }
      rewrite IHl; last first.
      { intros. destruct (Hin2 x) as [|Hin']; first by right.
        * auto. 
        * right. destruct Hin' as (i'&?&?&?). exists i'; split; auto. by right.
      }
      { intros; eapply Hin1; by right. }
      rewrite cost_bottom_cons1; last first.
      { eapply Hin2. by left. }
      { eapply Hin1. by left. } 
      rewrite cost_bottom_cons2; last first.
      { eapply Hin2. by left. }
      { eapply Hin1. by left. } 
      nra.
  Qed.

  Import countable.
  Import Series Hierarchy.

  Lemma ret_top_single a k:
    (INT_MIN < a < k)%Z →
    ret_top [:: a] k = a.
  Proof.
    intros (?&?). rewrite /ret_top//=.
    destruct Zbetween; last omega.
    rewrite /fold_left//=. rewrite Z.max_r //=. omega.
  Qed.

  Lemma bottom_split_list l1 l2 lb k:
    (k < INT_MAX)%Z →
    (∀ x, In x l1 → INT_MIN < x < k)%Z →
    (∀ x, In x l2 → x >= k ∧ INT_MIN < x < INT_MAX)%Z →
    (∀ x, In x l1 → ∀ x', In x' lb → x < x')%Z →
    (∀ x, In x lb → INT_MIN < x < k)%Z →
    StronglySorted Zgt l1 →
    Ex_ivd (λ ls, INR (cost_bottom (fst ls) (snd ls) k)) (single_skiplist (l1 ++ l2) [::] lb)
    = INR (length lb) + sum_n (fun i => (/2)^i) (length l1).
  Proof.
    revert lb. induction l1 => lb Hk Hl1_range Hl2_range Hl1_lb Hlb Hsort.
    - simpl single_skiplist. rewrite bottom_remaining_large; last first.
      { intros. left.  eapply Hl2_range. auto. }
      { intros. eapply Hl2_range. auto. }
      rewrite S_INR.
      rewrite /cost_bottom/ret_top//=.
      rewrite sum_O.
      replace (/2^0) with 1 by field.
      repeat f_equal. 
      apply list_between_all_in_range; eauto.
    - rewrite cat_cons.
      rewrite /single_skiplist -/single_skiplist.
      setoid_rewrite ivd_plus_bind.
      setoid_rewrite Ex_ivd_ivdplus.
      rewrite ?ivd_left_id.
      rewrite IHl1; last first; eauto.
      { apply StronglySorted_inv in Hsort; intuition. }
      { intros x [[]|Hin]; eauto.
        eapply Hl1_range; by left. }
      { intros x Hin x' [[]|Hin']; eauto. 
        ** apply StronglySorted_inv in Hsort as (?&Hsort).
           rewrite Forall_forall in Hsort * => Hsort.
           cut (a > x)%Z; first by omega.
           eapply Hsort. apply elem_of_list_In; eauto.
        ** eapply Hl1_lb; eauto. by right. }
      { intros. eapply Hl1_range; by right. }
      simpl length. rewrite S_INR. 
      rewrite bottom_remaining_large; last first.
      { intros x. rewrite in_app_iff. intros [Hin1|Hin2].
         * right. eexists; split; first by left.
           split.
           ** apply StronglySorted_inv in Hsort as (?&Hsort).
              rewrite Forall_forall in Hsort * => Hsort.
              cut (a > x)%Z; first by omega.
              eapply Hsort. apply elem_of_list_In; eauto.
           ** eapply Hl1_range; by left.
         * left. eapply Hl2_range; auto.
       }
      { intros x. rewrite in_app_iff. intros [Hin1|Hin2].
        * feed pose proof (Hl1_range x); first by right.
          omega.
        * eapply Hl2_range; auto.
      }
      rewrite /cost_bottom.
      rewrite ret_top_single; last first.
      { apply Hl1_range. by left. }
      simpl list_between.
      destruct Zbetween; first omega.
      rewrite list_between_all_in_range; last first.
      { intros i Hin; split.
        * apply Hl1_lb; auto; by left. 
        * apply Hlb; auto.
      }
      rewrite S_INR.
      ring_simplify.
      feed pose proof (sum_n_mult_l (1/2) (λ i, (/2) ^ i) (length l1)) as Hscal.
      rewrite /mult//= in Hscal.
      rewrite -Hscal.
      rewrite /sum_n.
      feed pose proof (sum_n_m_S (λ a, (/2)^a) 0 (length l1)) as Hshift.
      rewrite [a in a + _ + _ = _](sum_n_m_ext _ (λ a, (/2) ^ S a)); last first.
      { intros n'. rewrite //=. field. }
      rewrite Hshift.
      replace 1 with ((/2)^O); last by (rewrite //=; field).
      rewrite Rplus_assoc. rewrite Rplus_comm Rplus_assoc.
      f_equal.
  Qed.

  Lemma Ex_cost_bottom l k:
    NoDup l →
    (k < INT_MAX)%Z →
    (∀ x, In x l → INT_MIN < x < INT_MAX)%Z →
    Ex_ivd (λ ls, INR (cost_bottom (fst ls) (snd ls) k)) (single_skiplist l [::] [::])
    = 2 * (1 - (/2) ^ S (length (list_between l INT_MIN k))).
  Proof.
    intros HNoDup Hk Hin.
    edestruct (list_between_split l INT_MIN k) as (l1&l2&Hperm&Hl1&Hg2).
    assert (l1 = [::]).
    {  destruct l1 as [| z l1]; auto. exfalso. cut (INT_MIN < z ∧ z <= INT_MIN)%Z; first by omega.
       split.
       * eapply Hin. rewrite Hperm. apply in_app_iff.
         do 2 left => //=.
       * apply Hl1. by left.
    }
    subst. rewrite //= in Hperm. rewrite {1}Hperm.
    rewrite (ZSortGe.Permuted_sort (list_between l INT_MIN k)).
    rewrite bottom_split_list; last first.
    { apply Sorted_StronglySorted; first eauto with *.
      apply Sorted_Zge_NoDup_Zgt.
      * apply Sorted_ZorderGe_Zge, Sorted_sort_ge_folded.
      * rewrite -ZSortGe.Permuted_sort.
        rewrite /list_between.
        rewrite -filter_ssr_filter.
        apply NoDup_filter; auto.
    }
    { intros ? []. }
    { intros ? ? ? []. }
    { intros; split; eauto. eapply Hin.
      rewrite Hperm. apply in_app_iff. by right. }
    { intros x. rewrite -ZSortGe.Permuted_sort.
      apply list_between_In_inv1. }
    { auto. }
    simpl length. replace (INR 0) with 0 by auto. rewrite Rplus_0_l.
    rewrite sum_n_Reals tech3; last by nra.
    field.
  Qed.

  Lemma Ex_level2_cost l k:
    NoDup l →
    (k < INT_MAX)%Z →
    (∀ x, In x l → INT_MIN < x < INT_MAX)%Z →
    Ex_ivd (λ ls, INR (level2_cost (fst ls) (snd ls) k)) (single_skiplist l [::] [::])
                  = 1 + INR (length (list_between l INT_MIN k)) / 2 +
                    2 * (1 - (/2) ^ S (length (list_between l INT_MIN k))).
  Proof.
    intros.
    rewrite /level2_cost. setoid_rewrite plus_INR.
    rewrite Ex_ivd_sum.
    rewrite Ex_cost_top //= Ex_cost_bottom //=.
  Qed.

  Lemma Ex_skip_cost l k:
    NoDup l →
    (k < INT_MAX)%Z →
    (∀ x, In x l → INT_MIN < x < INT_MAX)%Z →
    Ex_ivd (λ ls, INR (skip_cost (fst ls) (snd ls) k)) (single_skiplist l [::] [::])
                  <= 1 + INR (length (list_between l INT_MIN k)) / 2 +
                    2 * (1 - (/2) ^ S (length (list_between l INT_MIN k))).
  Proof.
    intros. rewrite -Ex_level2_cost //.
    apply Ex_ival_mono. intros (lt&lb).
    apply le_INR. rewrite /skip_cost/level2_cost.
    destruct (decide _); omega.
  Qed.

  Lemma skiplist_ex_Ex (Skeys: gset Z) k:
    extrema.ex_Ex_extrema (λ ls, INR (skip_cost (fst ls) (snd ls) k))
                          (skiplist (elements Skeys) [::] [::]).
  Proof.
    apply extrema.ex_Ex_extrema_bounded_supp_fun.
    apply pspec_bounded. exists (INR (S (length (elements Skeys)) + S (length (elements Skeys)))).
    eapply pspec_conseq; first eapply (cost_bounded2 (elements Skeys) k).
    { eapply NoDup_elements. }
    intros (ls1&ls2). rewrite Rabs_right; last apply Rle_ge, pos_INR.
    intros Hle. apply le_INR. auto.
  Qed.

  Import Rbar.
  Lemma Rbar_le_finite (x y: R) :
    Rbar_le x y → x <= y.
  Proof. rewrite //=. Qed.

  Lemma skiplist_Ex_max (Skeys: gset Z) k:
    (k < INT_MAX)%Z →
    (∀ x, x ∈ Skeys → INT_MIN < x < INT_MAX)%Z →
    Rbar_le (extrema.Ex_max (λ ls, INR (skip_cost (fst ls) (snd ls) k))
                            (skiplist (elements Skeys) [::] [::]))
            (Rbar.Finite (1 + INR (length (list_between (elements Skeys) INT_MIN k)) / 2 +
                 2 * (1 - (/2) ^ S (length (list_between (elements Skeys) INT_MIN k))))).
  Proof.
    intros Hk Hin.
    rewrite skiplist_equiv_single; last first.
    { apply NoDup_ListNoDup, NoDup_elements. }
    rewrite Ex_max_singleton.
    rewrite //=.
    apply Ex_skip_cost.
    * apply NoDup_elements. 
    * auto.
    * intros x ?%elem_of_list_In. eapply Hin.
      apply elem_of_elements; auto.
  Qed.

End Skiplist_Expected.