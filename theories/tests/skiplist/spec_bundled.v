Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset agree gmap.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.
Set Default Proof Using "Type".

From iris.tests.skiplist Require Import code misc idxval spec_raw idxval_expected.

Module Skiplist_Spec (Params: SKIPLIST_PARAMS).
  Import Params.
  Module Expected := Skiplist_Expected Params. 
  Export Expected.
  Import Raw_spec.
  Export Code.

Definition skiplistΣ :=
  #[GFunctor (authR (gsetUR node_rep));
      GFunctor (authR (gsetUR node_rep));
      GFunctor (frac_authR (gsetUR node_rep));
      GFunctor (authR (gmapUR Z (agreeR nodeC)));
      GFunctor (gset_disjUR Z);
      GFunctor (authR (gsetUR Z));
      GFunctor (frac_authR (gsetUR Z))].

Global Instance subG_skiplistΣ {Σ} : subG skiplistΣ Σ → gset_list_unionG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{!heapG Σ, !probG Σ, !gset_list_unionG Σ, !lockG Σ}.

Record skip_gname :=
  mk_skip_gname
    {
    skip_t1: gname;
    skip_t2: gname;
    skip_t3: gname;
    skip_t4: gname;
    skip_b1: gname;
    skip_b2: gname;
    skip_b3: gname;
    skip_b4: gname;
    skip_st: gname;
    skip_sb1: gname;
    skip_sb2: gname
  }.

Definition skip_prop (Γ: skip_gname) q (nleft: val) (Sroot ST_keys SB_keys: gset Z) :=
  (∃ ST SB ST_map SB_map Nt Nb Ns np_left_top np_left_bottom
      (HkeT: key_equiv ST ST_keys)
      (HkeB: key_equiv SB SB_keys)
      (HmapT: is_map_of_nset ST ST_map)
      (HmapB: is_map_of_nset SB SB_map)
      (Hrange: ∀ k, k ∈ Sroot → INT_MIN < k ∧ k < INT_MAX)
      (Hnp_left_top: node_key (np_left_top) = INT_MIN)
      (Hnp_left_bot: node_key (np_left_bottom) = INT_MIN)
      (Hrep: rep_to_node np_left_top = nleft),
      inv Nt (link_map_inv (skip_t1 Γ) (skip_t2 Γ) (skip_t3 Γ) (skip_t4 Γ) np_left_top
                           (λ np, ∃ np', ⌜ node_val np = rep_to_node np' ∧
                                           node_key np = node_key np' ⌝ ∗
                                           (⌜ np' = np_left_bottom ⌝ ∨
                                            (own (skip_b1 Γ) (◯ {[ np' ]})
                                                 ∗ own (skip_sb1 Γ) (◯ {[ node_key np' ]})
             )))) ∗
      inv Nb (link_map_inv (skip_b1 Γ) (skip_b2 Γ) (skip_b3 Γ) (skip_b4 Γ) np_left_bottom
                               (λ np', ⌜ np' = np_left_bottom ⌝ ∨
                                        own (skip_sb1 Γ) (◯ {[ node_key np' ]}))%I) ∗
      inv Ns (skiplist_prob_inv (skip_st Γ) (skip_sb1 Γ) (skip_sb2 Γ) (skip_b3 Γ) Sroot) ∗
      own (skip_t2 Γ) (◯!{q} (ST : gset node_rep)) ∗
      own (skip_b2 Γ) (◯!{q} (SB : gset node_rep)) ∗
      own (skip_st Γ) (◯!{q} (ST_keys : gset Z)) ∗
      own (skip_sb2 Γ) (◯!{q} (SB_keys : gset Z)) ∗
      own (skip_t4 Γ) (◯ (ST_map : gmap Z (agree node_rep))) ∗
      own (skip_b4 Γ) (◯ (SB_map : gmap Z (agree node_rep)))
  )%I.

Global Instance skip_prop_Proper Γ q1 q2 v:
  Proper (equiv ==> equiv ==> equiv ==> eq) (skip_prop Γ q1 q2 v).
Proof.
  intros ?? Heq1 ?? Heq2 ?? Heq3.
  apply leibniz_equiv_iff in Heq1 as ->.
  apply leibniz_equiv_iff in Heq2 as ->.
  apply leibniz_equiv_iff in Heq3 as ->.
  done.
Qed.

Lemma skip_prop_sep Γ q1 q2 v S ST SB:
  skip_prop Γ (q1 + q2) v S ST SB ⊢ skip_prop Γ q1 v S ST SB ∗ skip_prop Γ q2 v S ST SB.
Proof.
  iIntros "H".
  iDestruct "H" as (ST' SB' ST_map' SB_map' Nt Nb Ns np_left_top) "H".
  iDestruct "H" as (np_left_bottom HkeT HkeB HmapT HmapB Hrange) "H".
  iDestruct "H" as (Hnp_left_top Hnp_left_bot Hrep) "H".
  iDestruct "H" as "(#Hi1&#Hi2&#Hi3&(Hown1&Hown1')&(Hown2&Hown2')&H)".
  iDestruct "H" as "((Hown3&Hown3')&(Hown4&Hown4')&#Hown5&#Hown5')". 
  iSplitL "Hown1 Hown2 Hown3 Hown4 Hown5".
  - unshelve (iExists ST', SB', ST_map', SB_map';
              repeat (iExists _); iFrame "∗"; iFrame "Hi1 Hi2 Hi3"); eauto.
  - unshelve (iExists ST', SB', ST_map', SB_map';
              repeat (iExists _); iFrame "∗"; iFrame "Hi1 Hi2 Hi3"); eauto.
Qed.

Lemma skip_prop_join Γ q1 q2 v S ST1 ST2 SB1 SB2:
  skip_prop Γ q1 v S ST1 SB1 ∗ skip_prop Γ q2 v S ST2 SB2
            ⊢ skip_prop Γ (q1 + q2) v S (ST1 ∪ ST2) (SB1 ∪ SB2).
Proof.
  iIntros "(H1&H2)".
  iDestruct "H1" as (ST' SB' ST_map' SB_map' Nt Nb Ns np_left_top) "H1".
  iDestruct "H1" as (np_left_bottom HkeT HkeB HmapT HmapB Hrange) "H1".
  iDestruct "H1" as (Hnp_left_top Hnp_left_bot Hrep) "H1".
  iDestruct "H1" as "(#Hi1&#Hi2&#Hi3&Hown1&Hown2&Hown3&Hown4&Hown5&Hown6)". 

  iDestruct "H2" as (ST2' SB2' ST_map2' SB_map2' Nt2 Nb2 Ns2 np_left_top2) "H2".
  iDestruct "H2" as (np_left_bottom2 HkeT2 HkeB2 HmapT2 HmapB2 Hrange2) "H2".
  iDestruct "H2" as (Hnp_left_top2 Hnp_left_bot2 Hrep2) "H2".
  iDestruct "H2" as "(#Hi1'&#Hi2'&#Hi3'&Hown1'&Hown2'&Hown3'&Hown4'&Hown5'&Hown6')". 

  iDestruct (own_valid_2 with "Hown5 Hown5'") as %Hval5.
  rewrite -auth_frag_op in Hval5. rewrite /valid/cmra_valid/auth_valid//= in Hval5.

  iDestruct (own_valid_2 with "Hown6 Hown6'") as %Hval6.
  rewrite -auth_frag_op in Hval6. rewrite /valid/cmra_valid/auth_valid//= in Hval6.

  iExists (ST' ∪ ST2'), (SB' ∪ SB2'), (ST_map' ⋅ ST_map2').
  iExists (SB_map' ⋅ SB_map2').
  unshelve (repeat (iExists _); iFrame "∗"; iFrame "Hi1 Hi2 Hi3"); eauto.
  * eapply key_equiv_union; eauto.
  * eapply key_equiv_union; eauto.
  * eapply is_map_of_nset_union; eauto.
  * eapply is_map_of_nset_union; eauto.
  * iCombine "Hown1 Hown1'" as "H"; iFrame "H".
    iCombine "Hown2 Hown2'" as "H"; iFrame "H".
    iCombine "Hown3 Hown3'" as "H"; iFrame "H".
    iCombine "Hown4 Hown4'" as "H"; iFrame "H".
    iCombine "Hown5 Hown5'" as "H"; iFrame "H".
    iCombine "Hown6 Hown6'" as "H"; iFrame "H".
Qed.

Lemma is_map_of_nset_empty: is_map_of_nset ∅ ∅.
  split; intros nr Hin.
    - inversion Hin.
    - destruct (∅ !! nr) eqn:Heq; auto.
      * inversion Heq. 
      * inversion 1.
Qed.
Hint Resolve is_map_of_nset_empty.
  
Lemma new_spec S (Hrange: ∀ k, k ∈ S → INT_MIN < k ∧ k < INT_MAX):
  {{{ ownProb (skiplist (elements S) [::] [::]) }}}
    newSkipList #()
  {{{ Γ v, RET v; skip_prop Γ 1%Qp v S ∅ ∅ }}}.
Proof.
  iIntros (Φ) "Hown HΦ".
  wp_apply (new_spec nroot nroot nroot with "Hown").
  iIntros (γt1 γt2 γt3 γt4 γb1 γb2 γb3 γb4 γst γsb1 γsb2).
  iIntros (np_left_top np_left_bottom).
  iIntros "(%&%&?&?&?&?&?&?&?&?&?)".
  iApply ("HΦ" $! (mk_skip_gname γt1 γt2 γt3 γt4 γb1 γb2 γb3 γb4 γst γsb1 γsb2)
               (rep_to_node np_left_top)).
  rewrite /skip_prop//=.
  iExists ∅, ∅, ∅, ∅.
  iExists nroot, nroot, nroot, np_left_top, np_left_bottom.
  unshelve (iExists _).
  { econstructor. }
  unshelve (iExists _).
  { econstructor. }
  unshelve (iExists _); auto.
  unshelve (iExists _); auto.
  iExists (Hrange).
  unshelve (iExists _); eauto.
  unshelve (iExists _); eauto.
  unshelve (iExists _); eauto.
  iFrame.
Qed.

Lemma add_spec Γ q v (S ST SB: gset Z) k (Hin: k ∈ S):
  {{{ skip_prop Γ q v S ST SB }}} 
    addSkipList v #k 
  {{{ (ST': gset Z), RET #(); skip_prop Γ q v S ST' (SB ∪ {[k]}) }}}.
Proof.
  iIntros (Φ) "H Hϕ".
  iDestruct "H" as (ST' SB' ST_map' SB_map' Nt Nb Ns np_left_top) "H".
  iDestruct "H" as (np_left_bottom HkeT HkeB HmapT HmapB Hrange) "H".
  iDestruct "H" as (Hnp_left_top Hnp_left_bot Hrep) "H".
  iDestruct "H" as "(#Hi1&#Hi2&#Hi3&Hown1&Hown2&Hown3&Hown4&Hown5&Hown6)". 
  rewrite -Hrep.
  wp_apply (add_spec Nt Nb Ns (skip_t1 Γ) (skip_t2 Γ) (skip_t3 Γ) (skip_t4 Γ)
                     (skip_b1 Γ) (skip_b2 Γ) (skip_b3 Γ) (skip_b4 Γ)
              with "[Hown1 Hown2 Hown3 Hown4 Hown5 Hown6]");
    try iFrame "Hi1 Hi2 Hi3";
    try iFrame; eauto.
  iIntros "H".
  iDestruct "H" as (ST'' ST''_keys ST''_map np'') "(%&?&?&?&?&?&?&%&%)".
  iApply ("Hϕ" $! ST''_keys).
  iExists ST'', (SB' ∪ {[np'']}).
  iExists ST''_map, (<[node_key np'':=to_agree np'']> SB_map').
  unshelve (repeat (iExists _); iFrame "Hi1 Hi2 Hi3"; iFrame); eauto.
  - intuition.
  - intuition.
Qed.

Lemma mem_full_spec Γ v (S ST SB: gset Z) k (Hrange: INT_MIN < k < INT_MAX):
  {{{ skip_prop Γ 1 v S ST SB }}} 
    memSkipList v #k 
    {{{ (b: bool) (z: Z), RET (#b, #z);
        skip_prop Γ 1 v S ST SB ∗
               ⌜ (if b then k ∈ SB else ¬ (k ∈ ST ∨ k ∈ SB)) ∧
                 z = skip_cost (elements (ST)) (elements (SB)) k ⌝
    }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iDestruct "H" as (ST' SB' ST_map' SB_map' Nt Nb Ns np_left_top) "H".
  iDestruct "H" as (np_left_bottom HkeT HkeB HmapT HmapB Hrange') "H".
  iDestruct "H" as (Hnp_left_top Hnp_left_bot Hrep) "H".
  iDestruct "H" as "(#Hi1&#Hi2&#Hi3&Hown1&Hown2&Hown3&Hown4&Hown5&Hown6)". 
  rewrite -Hrep.
  rewrite -wp_fupd.
  wp_apply (memSkipList_full_spec Nt Nb (skip_t1 Γ) (skip_t2 Γ) (skip_t3 Γ) (skip_t4 Γ)
                                  (skip_b1 Γ) (skip_b2 Γ) (skip_b3 Γ) (skip_b4 Γ)
              with "[Hown1 Hown2]");
    try iFrame "Hi1 Hi2 Hi3";
    try iFrame; eauto.
  iIntros (b z) "(HownT&HownB&%&Heq1&Heq2)".
  iDestruct "Heq1" as %Heq1.
  iDestruct "Heq2" as %Heq2.
  iInv Ns as "Hinv" "Hclose".
  iDestruct "Hinv" as (??) ">(%&HownST&HownSB1&HownSB2&Hrest)".
  iDestruct (own_valid_2 with "HownST Hown3") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "HownSB2 Hown4") as % ->%frac_auth_agreeL.
  iMod ("Hclose" with "[HownST HownSB1 HownSB2 Hrest]").
  { iExists _, _. iNext. iFrame. auto. }
  iModIntro.
  iApply "HΦ"; iSplit; auto.
  iExists ST', SB', ST_map', SB_map'.
  unshelve (repeat (iExists _); iFrame "Hi1 Hi2 Hi3"; iFrame); eauto.
  iPureIntro; split.
  { destruct b; auto; set_solver. }
  { rewrite /skip_cost. destruct (decide _) as [|Hn].
    * apply Heq1. apply elem_of_elements; eauto.
    * apply Heq2. rewrite elem_of_elements in Hn * => //=. }
Qed.

Lemma skip_prob_spec Γ v (S ST SB: gset Z):
  skip_prop Γ 1 v S ST SB ={⊤}=∗
            ownProb (skiplist (elements (S ∖ SB)) (elements ST) (elements SB)).
Proof.
  iIntros "H".
  iDestruct "H" as (ST' SB' ST_map' SB_map' Nt Nb Ns np_left_top) "H".
  iDestruct "H" as (np_left_bottom HkeT HkeB HmapT HmapB Hrange') "H".
  iDestruct "H" as (Hnp_left_top Hnp_left_bot Hrep) "H".
  iDestruct "H" as "(#Hi1&#Hi2&#Hi3&Hown1&Hown2&Hown3&Hown4&Hown5&Hown6)". 
  iInv Ns as "Hinv" "Hclose".
  iDestruct "Hinv" as (ST'' SB'') ">(%&HownST''&Ho1&HownSB''&Ho2&Hcase)".
  iDestruct (own_valid_2 with "HownST'' Hown3") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "HownSB'' Hown4") as % ->%frac_auth_agreeL.
  iDestruct "Hcase" as "[Hbad|Hown]".
  { iDestruct (own_valid_2 with "Hbad Hown4") as %?%frac_auth_frag_valid_op_1_l; done. }
  iMod ("Hclose" with "[HownST'' Ho1 HownSB'' Ho2 Hown4]").
  { iExists ST, SB; iNext. iSplit; auto.
    iFrame. iLeft. done. }
  iModIntro; auto.
Qed.

Lemma skip_prob_spec' Γ v (S ST: gset Z):
  skip_prop Γ 1 v S ST S ={⊤}=∗
            ownProb (mret (sort (elements ST), sort (elements S))).
Proof.
  iIntros "Hown".
  iMod (skip_prob_spec with "Hown").
  assert (Permutation (elements (S ∖ S)) [::]) as ->.
  { rewrite difference_diag elements_empty //=. }
  rewrite //=.
Qed.

End proof.
End Skiplist_Spec.