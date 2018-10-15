Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.

From iris.tests.skiplist Require Import code misc.


From discprob.idxval Require Import pival
     pival_dist fin_ival_dist irrel_equiv pidist_pair extrema pidist_post_cond.
From discprob.idxval Require Import fin_ival_pair pidist_fin_singleton.

Lemma list_exist {A: Type} (l: list A) (P: A → Prop) (Hall: ∀ x, List.In x l → P x) :
  list { x : A |  P x }.
Proof.
  induction l as [| a l IHl].
  - exact [::]. 
  - refine (exist _ a _ :: (IHl _)).
    * apply Hall. by left.
    * intros; apply Hall. by right.
Defined.

Lemma list_exist_spec1 {A: Type} (l: list A) P H:
  map (proj1_sig) (list_exist l P H) = l.
Proof.
  induction l; rewrite //=.
  f_equal; eauto.
Qed.

Lemma list_In {A: Type} (l: list A) : list { x : A | List.In x l}.
Proof. apply (list_exist l); trivial. Defined.

Require ProofIrrelevance.

Definition select_from_list_P {A: Type} (a: A) (l: seq A) (P : A → Prop)
           (HP: ∀ x, List.In x (a :: l) → P x) :
  pidist { x : A | P x }.
  apply (@pidist_join {x : A | List.In x (a :: l) }).
  { exists a; by left. }
  { intros (x&Hin). refine (mret (exist _ x (HP _ Hin))). }
Defined.

Definition select_from_list {A: Type} (a: A) (l: seq A) : pidist A.
  apply (@pidist_join {x : A | List.In x (a :: l) }).
  { exists a; by left. }
  { intros (x&Hin). exact (mret x). }
Defined.

Lemma select_from_list_P_non_dep_eq {A: Type} (a : A) l P HP:
  eq_pidist (x ← select_from_list_P a l P HP; mret (`x))
            (select_from_list a l).
Proof.
  rewrite /select_from_list_P/select_from_list. setoid_rewrite pidist_join_bind.
  etransitivity.
  { eapply (pidist_join_ext _ ((a ↾ or_introl eq_refl)) _
                            (λ x, z ← mret (exist _ (proj1_sig x) (HP (proj1_sig x) (proj2_sig x)));
                             mret (`z))).
    intros (?&?). rewrite //=.
  }
  setoid_rewrite pidist_left_id => //=.
  eapply pidist_join_ext.
  intros (?&?) => //=.
Qed.

Definition select_from_list_dep {A: Type} (a: A) (l: seq A) : pidist { x : A | List.In x (a :: l) }.
  apply (select_from_list_P a l); trivial.
Defined.

Lemma select_from_list_dep_eq {A: Type} (a : A) l:
  eq_pidist (x ← select_from_list_dep a l; mret (`x))
            (select_from_list a l).
Proof. eapply select_from_list_P_non_dep_eq. Qed.

From Coq Require Import Program.Wf.

Lemma flip12: (0 <= 1 / 2)%R ∧ (1 / 2 <= 1)%R.
Proof. nra. Qed.

Import List seq.

(* Main pidist that we prove a coupling with; not structurally recursive
   (because you select any element from the list)
*)

Definition skiplist (add_list top_list bottom_list: list Z) :
  pidist (list Z * list Z).
Proof.
  refine (Fix (measure_wf lt_wf length) (fun _ => list Z → list Z → pidist (list Z * list Z))
              (fun (l: list Z) skiplist =>
                λ tl bl,
                match l as l' return (l = l' → pidist (list Z * list Z)) with
                | [::] => λ eq, mret (sort tl, sort bl)
                | (a :: l) =>
                  λ eq,
                  kchoice ← select_from_list_dep a l;
                  tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (proj1_sig kchoice :: tl));
                  skiplist (remove Z_eq_dec (proj1_sig kchoice) (a :: l)) _ tl'
                           (proj1_sig kchoice :: bl)
                end (Init.Logic.eq_refl)) add_list top_list bottom_list).
  rewrite /MR eq.
  apply length_remove_lt. destruct kchoice; auto.
Defined.

Lemma skiplist_unfold_aux (l: list Z) tl bl:
  skiplist l tl bl =
    match l as l' return (l = l' → pidist (list Z * list Z)) with
    | [::] => λ eq, mret (sort tl, sort bl)
    | (a :: l) =>
      λ eq,
      kchoice ← select_from_list_dep a l;
      tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (proj1_sig kchoice :: tl));
      skiplist (remove Z_eq_dec (proj1_sig kchoice) (a :: l)) tl'
               (proj1_sig kchoice :: bl)
    end (Init.Logic.eq_refl).
Proof. rewrite /skiplist pival_dist.easy_fix_eq; done. Qed.

Lemma skiplist_unfold l tl bl:
  skiplist l tl bl =
    match l with
    | [::] => mret (sort tl, sort bl)
    | (a :: l) =>
      kchoice ← select_from_list_dep a l;
      tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (proj1_sig kchoice :: tl));
      skiplist (remove Z_eq_dec (proj1_sig kchoice) (a :: l)) tl'
               (proj1_sig kchoice :: bl)
    end.
Proof. rewrite skiplist_unfold_aux //=. destruct l; auto. Qed.

Lemma skiplist_unfold_non_dep l tl bl:
  eq_pidist (skiplist l tl bl)
            match l with
            | [::] => mret (sort tl, sort bl)
            | (a :: l) =>
              kchoice ← select_from_list a l;
                tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (kchoice :: tl));
                skiplist (remove Z_eq_dec kchoice (a :: l)) tl'
                         (kchoice :: bl)
            end.
Proof.
  rewrite skiplist_unfold.
  destruct l.
  * reflexivity.
  * setoid_rewrite <-select_from_list_dep_eq.
    setoid_rewrite pidist_assoc.
    eapply pidist_bind_congr; first reflexivity.
    intros (x&Hin).
    rewrite pidist_left_id. reflexivity.
Qed.

Lemma select_from_list_perm_eq {A: Type} (a a' : A) l l':
  Permutation (a :: l) (a' :: l') →
  eq_pidist (select_from_list a l) (select_from_list a' l').
Proof.
  intros Hperm.
  split.
  - intros I ((x&Hinl)&Hin).
    exists I; split; auto.
    unshelve (eexists).
    { exists x.
      abstract (apply elem_of_list_In; rewrite -Hperm; apply elem_of_list_In; done).
    }
    rewrite //=.
  - intros I ((x&Hinl)&Hin).
    exists I; split; auto.
    unshelve (eexists).
    { exists x.
      abstract (apply elem_of_list_In; rewrite Hperm; apply elem_of_list_In; done).
    }
    rewrite //=.
Qed.

Lemma skiplist_perm_eq l tl bl l' tl' bl':
  Permutation l l' →
  Permutation tl tl' →
  Permutation bl bl' →
  eq_pidist (skiplist l tl bl) (skiplist l' tl' bl').
Proof.
  remember (length l) as n eqn:Heq.
  revert l Heq l' tl bl tl' bl'.
  induction n as [n IHn] using lt_wf_ind  => l Heq_length l' tl bl tl' bl' Hperm1 Hperm2 Hperm3.
  destruct l as [|a l].
  - apply Permutation.Permutation_nil in Hperm1. subst.
    rewrite ?skiplist_unfold //=.
    assert (sort tl = sort tl') as ->.
    { apply Sorted_Zle_uniq.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * rewrite -?Permuted_sort. done.
    }
    assert (sort bl = sort bl') as ->.
    { apply Sorted_Zle_uniq.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * rewrite -?Permuted_sort. done.
    }
    reflexivity.
  - destruct l' as [| a' l'].
    { exfalso. symmetry in Hperm1. apply Permutation.Permutation_nil in Hperm1. congruence. }
    apply pidist_coupling_eq.
    eapply pidist_coupling_ext.
    { rewrite skiplist_unfold_non_dep. reflexivity. }
    { rewrite skiplist_unfold_non_dep. reflexivity. }
    { reflexivity. }
    eapply (pidist_coupling_bind _ _ _ _ (λ x y, x = y ∧ List.In x (a :: l) ∧ List.In y (a :: l))).
    {
      unshelve (econstructor).
      { refine (x ← select_from_list_dep a l; mret _). 
        destruct x as (x&Hin). exists (x, x); split_and! => //=. }
      * rewrite -select_from_list_dep_eq. 
        setoid_rewrite pidist_assoc. apply pidist_bind_congr; first reflexivity.
        intros (?&?). setoid_rewrite pidist_left_id => //=.
      * rewrite -select_from_list_perm_eq; last eauto.
        rewrite -select_from_list_dep_eq. 
        setoid_rewrite pidist_assoc. apply pidist_bind_congr; first reflexivity.
        intros (?&?). setoid_rewrite pidist_left_id => //=.
    }
    intros ?? (<-&?&?).
    apply pidist_coupling_eq_inv.
    setoid_rewrite pidist_plus_bind.
    apply pidist_plus_proper; setoid_rewrite pidist_left_id.
    * eapply IHn; eauto.
      ** rewrite Heq_length. apply length_remove_lt; auto.
      ** apply remove_perm_proper; eauto.
    * eapply IHn; eauto.
      ** rewrite Heq_length. apply length_remove_lt; auto.
      ** apply remove_perm_proper; eauto.
Qed.

Global Instance skiplist_perm_eq_Proper:
  Proper (Permutation ==> Permutation ==> Permutation ==> eq_pidist) skiplist.
Proof.
  intros ?? Hperm ?? Hperm' ?? Hperm''.
  eapply skiplist_perm_eq; eauto.
Qed.

Lemma select_from_list_hd {A: Type} (a: A) tl :
  le_pidist (mret a) (select_from_list a tl).
Proof.
  rewrite /select_from_list.
  intros I Hin. exists I; split; first reflexivity.
  exists (exist _ a (or_introl eq_refl)). done.
Qed.


Lemma skiplist_unfold_choice a l tl bl:
  ¬ (a ∈ l) →
  le_pidist
    (tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (a :: tl));
       skiplist l tl' (a :: bl))
    (skiplist (a :: l) tl bl).
Proof.
  intros Hnin.
  rewrite skiplist_unfold_non_dep.
  transitivity
    (x ← mret a;
     tl' ← pidist_plus (1/2) flip12 (mret tl) (mret (x :: tl));
     skiplist l tl' (x :: bl)).
  { setoid_rewrite pidist_left_id. reflexivity. }
  apply pidist_bind_congr_le_supp.
  { apply select_from_list_hd. }
  { intros ? ?%In_psupport_mret_inv. subst.
    apply pidist_bind_congr_le; first reflexivity.
    intros.
    rewrite //= remove_not_in //=. 
    destruct Z_eq_dec => //=.
  }
Qed.


(* We prove that the skiplist is equivalent to a singleton indexed valuation
   which simply adds the items in the list in the order they occur... the result is
   structurally recursive and much easier to reason about *)

Fixpoint single_skiplist (al tl bl: list Z) : ivdist (list Z * list Z) :=
  match al with
  | [::] => mret (sort tl, sort bl)
  | (a :: l) =>
    tl' ← ivdplus (1/2) flip12 (mret tl) (mret (a :: tl));
      single_skiplist l tl' (a :: bl)
  end.

Fixpoint single_skiplist_alt (al tl bl: list Z) : ivdist (list Z * list Z) :=
  match al with
  | [::] => mret (sort tl, sort bl)
  | (a :: l) =>
    hd ← ivdplus (1/2) flip12 (mret [::]) (mret [::a]);
    single_skiplist_alt l (hd ++ tl) (a :: bl)
  end.

Lemma single_skiplist_alt_equiv al tl bl:
  eq_ivd (single_skiplist al tl bl) (single_skiplist_alt al tl bl).
Proof.
  revert tl bl.
  induction al => tl bl.
  - rewrite //=. 
  - apply ival_coupling_eq.
    rewrite /single_skiplist -/single_skiplist.
    rewrite /single_skiplist_alt -/single_skiplist_alt.
    apply ival_coupling_bind with (P := λ tl' hd, hd ++ tl = tl').
    { apply ival_coupling_plus.
      * apply ival_coupling_mret. rewrite //=. 
      * apply ival_coupling_mret. rewrite //=. 
    }
    intros x y ->. 
    eapply ival_coupling_proper.
    { reflexivity. }
    { eapply IHal. }
    apply ival_coupling_refl.
Qed.

Lemma single_skiplist_alt_perm_aux l tl bl tl' bl':
  Permutation tl tl' →
  Permutation bl bl' →
  eq_ivd (single_skiplist_alt l tl bl) (single_skiplist_alt l tl' bl').
Proof.
  revert tl bl tl' bl'.
  induction l as [| a l] => tl bl tl' bl' Hperm2 Hperm3.
  - rewrite //=. 
    assert (sort tl = sort tl') as ->.
    { apply Sorted_Zle_uniq.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * rewrite -?Permuted_sort. done.
    }
    assert (sort bl = sort bl') as ->.
    { apply Sorted_Zle_uniq.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * apply Sorted_Zorder_Zle, Sorted_sort_folded.
      * rewrite -?Permuted_sort. done.
    }
    reflexivity.
  - eapply ivd_bind_congr; first reflexivity.
    intros; eapply IHl; rewrite ?Hperm2 ?Hperm3 //=.
Qed.

Import monad.

Lemma single_skiplist_alt_perm l tl bl l' tl' bl':
  Permutation l l' →
  Permutation tl tl' →
  Permutation bl bl' →
  eq_ivd (single_skiplist_alt l tl bl) (single_skiplist_alt l' tl' bl').
Proof.
  intros Hperm1.
  revert tl bl tl' bl'.
  induction Hperm1 => tl bl tl' bl' Hperm2 Hperm3;
                        try eapply single_skiplist_alt_perm_aux; eauto.
  - apply ivd_bind_congr; first reflexivity.
    intros. eapply IHHperm1; rewrite ?Hperm2 ?Hperm3 //=.
  - rewrite {1}/single_skiplist_alt -/single_skiplist_alt.
    rewrite /eq_ivd. setoid_rewrite fin_ival.ival_bind_comm at 1.
    rewrite {2}/single_skiplist_alt -/single_skiplist_alt.
    eapply fin_ival.ival_bind_congr; first reflexivity.
    intros l1.
    eapply fin_ival.ival_bind_congr; first reflexivity.
    intros l2.
    apply single_skiplist_alt_perm_aux; rewrite ?Hperm2 ?Hperm3 //=; last by econstructor.
    rewrite ?app_cat.
    rewrite ?app_assoc (Permutation_app_comm l1) //=.
  - setoid_rewrite IHHperm1_1; eauto.
Qed.

Lemma single_skiplist_perm l tl bl l' tl' bl':
  Permutation l l' →
  Permutation tl tl' →
  Permutation bl bl' →
  eq_ivd (single_skiplist l tl bl) (single_skiplist l' tl' bl').
Proof.
  intros.
  setoid_rewrite single_skiplist_alt_equiv.
  apply single_skiplist_alt_perm; auto.
Qed.

Global Instance single_skiplist_Perm_proper:
  Proper (Permutation ==> Permutation ==> Permutation ==> eq_ivd) single_skiplist.
Proof.
  intros ?? Hperm1 ?? Hperm2 ?? Hperm3.
  apply single_skiplist_perm; eauto.
Qed.
  


Lemma skiplist_equiv_single l tl bl:
  NoDup l →
  eq_pidist (skiplist l tl bl) (singleton (single_skiplist l tl bl)).
Proof.
  remember (length l) as n eqn:Heq.
  revert l Heq tl bl.
  induction n as [n IHn] using lt_wf_ind  => l Heq tl bl HNoDup.
  destruct l as [| a l].
  - rewrite skiplist_unfold //= singleton_mret //=.
  - rewrite skiplist_unfold.
    rewrite -[a in eq_pidist _ a](pidist_left_id tt (λ _, singleton _)).
    apply pidist_coupling_eq.
    eapply (pidist_coupling_bind) with (P := λ x y, True).
    {  apply pidist_coupling_join.
       intros (x&Hin) => //=.
       apply pidist_coupling_mret => //=.
    }
    intros (a'&Hin) _ _.
    feed pose proof (in_split a' (a :: l)) as Hex; auto.
    apply ClassicalEpsilon.constructive_indefinite_description in Hex as (l1&Hex).
    apply ClassicalEpsilon.constructive_indefinite_description in Hex as (l2&Hex).
    assert (Permutation (a :: l) (a' :: (l1 ++ l2))) as Hperm.
    { rewrite Hex.
      rewrite Permutation_app_comm.
      rewrite -app_comm_cons.
      rewrite Permutation_app_comm.
      rewrite -?app_cat //=.
    }
    eapply pidist_coupling_ext.
    { reflexivity. }
    { setoid_rewrite Hperm. reflexivity. }
    { reflexivity. }
    apply pidist_coupling_eq_inv.
    rewrite /single_skiplist -/single_skiplist.
    setoid_rewrite singleton_bind.
    apply pidist_bind_congr.
    { rewrite singleton_plus ?singleton_mret //=. }
    intros l'.
    rewrite /proj1_sig.
    assert (Permutation (remove Z_eq_dec a' (a :: l)) (l1 ++ l2)) as ->.
    { rewrite remove_perm_proper; last eassumption.
      rewrite //=; destruct Z_eq_dec; last omega.
      rewrite remove_not_in; first reflexivity.
      rewrite Hperm in HNoDup * => HND.  
      inversion HND; subst. rewrite elem_of_list_In; eauto.
    }
    eapply IHn; eauto.
    * rewrite Heq.
      rewrite (Permutation_length Hperm) => //=.
      omega.
    * rewrite Hperm in HNoDup *. inversion 1; subst; eauto.
Qed.
