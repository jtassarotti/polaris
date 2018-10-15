Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset agree gmap.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.

From iris.tests.skiplist Require Import code misc idxval spec_bundled idxval_expected.

Module P <: SKIPLIST_PARAMS.
  Definition INT_MIN := -1000%Z.
  Definition INT_MAX := 1000%Z.
  Lemma HMIN_MAX : (INT_MIN < INT_MAX)%Z.
  Proof. rewrite /INT_MIN/INT_MAX. by omega. Qed.
End P.

Module Import Spec := Skiplist_Spec P.
Import Raw_spec.
Import Raw_spec.Code.
Import Spec.

(* Convert a list of Coq ints into a heap_lang tuple *)
Fixpoint l2tuple (l: list Z) : val :=
  match l with
  | [] => NONEV
  | z :: l =>
    SOMEV (#z, l2tuple l)
  end.

Definition foldLeft : val :=
  rec: "foldLeft" "f" "l" "a" :=
    match: "l" with
      NONE => "a"
    | SOME "cell" =>
      "foldLeft" "f" (Snd "cell") ("f" "a" (Fst "cell"))
    end.

Definition addList : val := 
  λ: "slist" "lz",
  foldLeft (λ: <> "c", addSkipList "slist" "c") "lz" #().

Definition skip_list_client l1 l2 (k: Z): expr := 
  let: "slist" := newSkipList #() in
  (addList "slist" (l2tuple l1)  ||| addList "slist" (l2tuple l2)) ;;
  memSkipList "slist" #k.

Section proof.
Context `{!heapG Σ, !probG Σ, !gset_list_unionG Σ, !lockG Σ, spawnG Σ}.

Lemma set_of_list_cons (z: Z) lb: set_of_list (z :: lb) = {[z]} ∪ set_of_list lb.
Proof.
  rewrite -leibniz_equiv_iff. intros x.
  rewrite elem_of_union -?elements_set_of_list elem_of_singleton //=; set_solver.
Qed.

Lemma addList_spec Γ q v S ST SB ladd:
  (∀ x, x ∈ ladd → x ∈ S) →
  {{{ skip_prop Γ q v S ST SB }}}
    addList v (l2tuple ladd)
  {{{ ST', RET #(); skip_prop Γ q v S ST' (SB ∪ set_of_list ladd) }}}.
Proof.
  iIntros (Hin Φ) "HA Hwand". 
  wp_let. wp_let. wp_let. wp_let. wp_let.
  iRevert (ladd ST SB Hin) "HA Hwand".
  iLöb as "IH". iIntros (lb ST SB Hin) "Hlist Hwand".
  destruct lb.
  * wp_match. iApply ("Hwand" $! ST).
    replace (set_of_list [::]) with (∅ : gset Z); last by rewrite //=.
    {
      replace (SB ∪ ∅) with SB; last first.
      { rewrite -leibniz_equiv_iff right_id //=. }
      done.
    }
  * rewrite /l2tuple -/l2tuple.
    wp_match. wp_let. wp_proj.
    wp_let. wp_let. wp_proj. wp_let.
    wp_apply (add_spec with "Hlist").
    { apply Hin. by left. }
    iIntros (ST') "Hlist".
    wp_let.  iApply ("IH" with "[] Hlist [Hwand]").
    { iPureIntro => x ?. apply Hin. by right. }
    iIntros (ST'') "Hskip".
    iApply ("Hwand" $! ST'').
    assert (SB ∪ set_of_list (z :: lb) = SB ∪ {[z]} ∪ set_of_list lb) as ->; auto.
    { rewrite set_of_list_cons. set_solver. }
Qed.

Lemma skip_list_client_spec l1 l2 k:
  (P.INT_MIN < k ∧ k < P.INT_MAX)%Z →
  (∀ k, k ∈ l1 ∨ k ∈ l2 → P.INT_MIN < k < P.INT_MAX) →
  ownProb (skiplist (elements (set_of_list l1 ∪ set_of_list l2)) [::] [::]) ⊢
          WP (skip_list_client l1 l2 k)
          {{ v, ∃ (ST : gset Z) (cmps: Z),
               ownProb (mret (sort (elements ST),
                              sort (elements (set_of_list l1 ∪ set_of_list l2))))
           ∗ ⌜ v = ((if decide (k ∈ l1 ∨ k ∈ l2) then #true else #false), #cmps)%V 
               ∧ cmps = skip_cost (elements ST)
                                  (elements (set_of_list l1 ∪ set_of_list l2))
                                  k⌝ }}%I.
Proof.
  iIntros (Hkrange Hrange) "Hprob". rewrite /skip_list_client.
  wp_bind (newSkipList _).
  wp_apply (new_spec with "Hprob").
  { intros k'. rewrite elem_of_union -?elements_set_of_list //=. apply Hrange. }
  iIntros (Γ v) "Hskip".
  rewrite -(Qp_div_2 1).
  rewrite skip_prop_sep.
  iDestruct "Hskip" as "(Hskip1&Hskip2)".
  wp_let.
  wp_apply (wp_par (λ _, ∃ ST', skip_prop Γ (1 / 2)%Qp v (set_of_list l1 ∪ set_of_list l2)
                                          ST' (set_of_list l1))%I
                   (λ _, ∃ ST', skip_prop Γ (1 / 2)%Qp v (set_of_list l1 ∪ set_of_list l2)
                                          ST' (set_of_list l2))%I
                      with "[Hskip1] [Hskip2]").
  - wp_apply (addList_spec with "Hskip1").
    { intros x. rewrite elem_of_union elements_set_of_list //=. set_solver. }
    iIntros (ST') "H". iExists ST'.
    replace (∅ ∪ set_of_list l1) with (set_of_list l1) by set_solver.
    done.
  - wp_apply (addList_spec with "Hskip2").
    { intros x. rewrite elem_of_union elements_set_of_list //=. set_solver. }
    iIntros (ST') "H". iExists ST'.
    replace (∅ ∪ set_of_list l2) with (set_of_list l2) by set_solver.
    done.
  - iIntros (v1 v2) "(Hpost1&Hpost2)".
    iDestruct "Hpost1" as (ST1') "Hpost1".
    iDestruct "Hpost2" as (ST2') "Hpost2".
    iCombine "Hpost1" "Hpost2" as "Hpost".
    rewrite skip_prop_join Qp_div_2.
    iNext. wp_let.
    rewrite -wp_fupd.
    wp_apply (mem_full_spec with "Hpost"); eauto.
    { iIntros (b z) "(Hskip&Hpure)".
      iDestruct "Hpure" as %(Hin1&Heq).
      iMod (skip_prob_spec' with "Hskip") as "Hown".
      iModIntro.
      iExists _, z. iFrame. 
      iPureIntro; split.
      * f_equal.  destruct b; destruct decide; auto.
        ** rewrite elem_of_union -?elements_set_of_list in Hin1 *; intuition.
        ** setoid_rewrite elem_of_union in Hin1.
           destruct Hin1. rewrite -?elements_set_of_list; intuition.
      * auto. 
    }
Qed.
End proof.

Section adequate.
Let Σ : gFunctors := #[ heapΣ ; spawnΣ; lockΣ; skiplistΣ].

Definition client_ival sch e σ k := @ivdist_tpool_stepN heap_ectxi_lang sch [e] σ k.
Import pival pival_dist ival_dist irrel_equiv idist_pidist_pair extrema pidist_post_cond.

Global Instance skip_cost_perm_Proper:
  Proper (Permutation ==> Permutation ==> eq ==> eq) skip_cost.
Proof.
  intros l1 l2 Hperm l1' l2' Hperm' k1 k2 ->.
  rewrite /skip_cost.
  assert (k2 ∈ l1 ↔ k2 ∈ l2).
  { rewrite Hperm. auto. }
  do 2 destruct (decide _); try intuition; rewrite /level2_cost/cost_top/cost_bottom;
    rewrite -?Hperm -?Hperm' //=.
Qed.

Lemma generic_client_adequate n sch e σ k (Sroot: gset Z):
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (skiplist (elements Sroot) [::] [::]) -∗
   WP e {{ v, ∃ (ST : gset Z) (b: bool) (cmps: Z),
               ownProb (mret (sort (elements ST),
                              sort (elements Sroot))) ∗
           ⌜ v = (#b, #cmps)%V ∧ (cmps = skip_cost (elements ST) (elements Sroot) k)%Z⌝ }})%I →
                                                                                           
  terminates sch [([e], σ)] n →
  irrel_couplingP (client_ival sch e σ n)
                  (skiplist (elements Sroot) [::] [::])
                  (prob_adequacy.coupling_post
                     (λ x y, ∃ b (cmps: Z), x = (#b, #cmps)%V
                             ∧ (cmps = skip_cost (fst y) (snd y) k)%Z)).
Proof.
  intros Hspec ?.
  eapply (heap_prob_adequacy Σ (skiplist (elements Sroot) [::] [::])
                             e σ _ sch n); eauto.
  intros. iIntros "Hprob".
  iApply wp_wand_r; iSplitL "Hprob".
  { iApply Hspec; done. }
  iIntros (v) "H".
  iDestruct "H" as (ST b cmps) "(Hown&%&Hp)".
  iDestruct "Hp" as %Heq.
  iExists (_, _); iFrame. iPureIntro. do 2 eexists; split; eauto.
  rewrite Heq. rewrite //=. rewrite -?Permuted_sort //.
Qed.

Open Scope R_scope.
Import Rbar.

Lemma list_client_ex_Ex_ival lb1 lb2 sch σ n k rank:
  (P.INT_MIN < k < P.INT_MAX)%Z →
  (∀ k, k ∈ lb1 ∨ k ∈ lb2 → P.INT_MIN < k < P.INT_MAX)%Z →
  terminates sch [([skip_list_client lb1 lb2 k], σ)] n →
  rank = (length (list_between (elements (set_of_list lb1 ∪ set_of_list lb2)) P.INT_MIN k)) →
  ex_Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (PairV _ (LitV (LitInt y))) => IZR y
                            | _ => 0
                            end
                end)
          (client_ival sch (skip_list_client lb1 lb2 k) σ n).
Proof.
  intros Hkrange Hrange; intros.
  eapply irrel_coupling_eq_ex_Ex_supp with (g := (λ ls, INR (skip_cost (fst ls) (snd ls) k))).
    eapply irrel_coupling_conseq; last first.
    * apply generic_client_adequate; auto.
      iIntros (??) "Hprob".
      iApply wp_wand_r; iSplitL "Hprob".
      { iApply skip_list_client_spec; eauto. }
      iIntros (?) "H". iDestruct "H" as (ST cmps) "H".
      iExists ST, (if decide (k ∈ lb1 ∨ k ∈ lb2) then true else false), cmps.
      destruct (decide _);
      iFrame "H".
    * intros x y. 
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      intros (?&?&->&->). 
      rewrite INR_IZR_INZ. done.
    * apply pspec_bounded. eexists (INR (S (length (elements _)) + S (length (elements _)))).
      eapply pspec_conseq; first eapply (cost_bounded2
                                           (elements (set_of_list lb1 ∪ set_of_list lb2)) k).
      { eapply NoDup_elements. }
      intros (ls1&ls2). rewrite Rabs_right; last apply Rle_ge, pos_INR.
      intros Hle. apply le_INR. auto.
     eapply Hle.
Qed.

Lemma list_client_Ex_ival lb1 lb2 sch σ n k rank:
  (P.INT_MIN < k < P.INT_MAX)%Z →
  (∀ k, k ∈ lb1 ∨ k ∈ lb2 → P.INT_MIN < k < P.INT_MAX)%Z →
  terminates sch [([skip_list_client lb1 lb2 k], σ)] n →
  rank = (length (list_between (elements (set_of_list lb1 ∪ set_of_list lb2)) P.INT_MIN k)) →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (PairV _ (LitV (LitInt y))) => IZR y
                            | _ => 0
                            end
                end)
          (client_ival sch (skip_list_client lb1 lb2 k) σ n)
  <= (1 + INR rank / 2 + 2 * (1 - (/2) ^ S rank)).
Proof.
  intros Hkrange Hrange; intros.
  apply Rbar_le_finite.
  etransitivity.
  - eapply irrel_coupling_eq_Ex_max_supp with (g := (λ ls, INR (skip_cost (fst ls) (snd ls) k))).
    eapply irrel_coupling_conseq; last first.
    * apply generic_client_adequate; auto.
      iIntros (??) "Hprob".
      iApply wp_wand_r; iSplitL "Hprob".
      { iApply skip_list_client_spec; eauto. }
      iIntros (?) "H". iDestruct "H" as (ST cmps) "H".
      iExists ST, (if decide (k ∈ lb1 ∨ k ∈ lb2) then true else false), cmps.
      destruct (decide _);
      iFrame "H".
    * intros x y. 
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      intros (?&?&->&->). 
      rewrite INR_IZR_INZ. done.
    * apply pspec_bounded. eexists (INR (S (length (elements _)) + S (length (elements _)))).
      eapply pspec_conseq; first eapply (cost_bounded2
                                           (elements (set_of_list lb1 ∪ set_of_list lb2)) k).
      { eapply NoDup_elements. }
      intros (ls1&ls2). rewrite Rabs_right; last apply Rle_ge, pos_INR.
      intros Hle. apply le_INR. auto.
     eapply Hle.
  - subst. apply skiplist_Ex_max.
    * intuition; eauto.
    * intros. eapply Hrange. rewrite ?elements_set_of_list //. set_solver.
Qed.
End adequate.