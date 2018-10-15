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

From iris.tests.skiplist Require Import code misc idxval.

Module Skiplist_Raw_Spec (Params: SKIPLIST_PARAMS).
  Import Params.
  Module Code := Skiplist Params. 
  Export Code.

From discprob.idxval Require Import pival
     pival_dist ival_dist irrel_equiv idist_pidist_pair pidist_pair extrema pidist_post_cond.

Canonical Structure nodeC := leibnizC (node_rep).

Class gset_list_unionG Σ :=
  GsetG { gset_nr_A_inG :> inG Σ (authR (gsetUR node_rep));
          gset_nr_F_inG :> inG Σ (frac_authR (gsetUR node_rep));
          gset_nr_M_inG :> inG Σ (authR (gmapUR Z (agreeR nodeC)));
          gset_Z_disj_inG :> inG Σ (gset_disjUR Z);
          gset_Z_A_inG :> inG Σ (authR (gsetUR Z));
          gset_Z_F_inG :> inG Σ (frac_authR (gsetUR Z));
        }.

Section proof.
Context `{!heapG Σ, !probG Σ, !gset_list_unionG Σ, !lockG Σ}.



Fixpoint link_map_rep (γz: gname) (L: list node_rep) P : iProp Σ :=
  (match L with
   | nil => True%I
   | np :: L =>
     match L with
       | nil => 
         (node_next np) ↦{1/2} rep_to_node right_sentinel ∗
                        (∃ γ N, is_lock γ N (node_lock np)
                                        (∃ np'', node_next np ↦{1/2} rep_to_node np'' ∗
                                                 own γz (GSet (Zlt_range (node_key np)
                                                                         (node_key np''))))) ∗ 
                        P np ∗
                        link_map_rep γz L P
       | np' :: L' =>
         (node_next np) ↦{1/2} rep_to_node np' ∗
                        (∃ γ N, is_lock γ N (node_lock np)
                                        (∃ np'', node_next np ↦{1/2} rep_to_node np'' ∗
                                                 own γz (GSet (Zlt_range (node_key np)
                                                                         (node_key np''))))) ∗ 
                        P np ∗
                        link_map_rep γz L P
     end
  end)%I.

Lemma link_map_rep_unfold2 γz np np' L P:
  link_map_rep γz [:: np, np' & L] P =
         ((node_next np) ↦{1/2} rep_to_node np' ∗
                        (∃ γ N, is_lock γ N (node_lock np)
                                        (∃ np'', node_next np ↦{1/2} rep_to_node np'' ∗ 
                                                 own γz (GSet (Zlt_range (node_key np)
                                                                         (node_key np''))))) ∗ 
                        P np ∗
                        link_map_rep γz (np' :: L) P)%I.
Proof. rewrite //=. Qed.
  
     
Lemma link_map_rep_cons_invert γz np (L: list node_rep) P :
  link_map_rep γz (np :: L) P
               ⊢ link_map_rep γz L P ∗ (link_map_rep γz L P -∗ link_map_rep γz (np :: L) P).
Proof.
  destruct L.
  * iIntros "(?&Hinv&?)".
    iFrame. done.
  * iIntros "(?&Hinv&?&?)". iFrame. auto.
Qed.

Lemma link_map_rep_P_hd γz np L P:
  link_map_rep γz (np :: L) P ⊢ P np.
Proof.
  rewrite //=. destruct L; iIntros "(?&?&?&?)"; iFrame.
Qed.

Import List seq.
  
Lemma link_map_rep_invert γz np (L: list node_rep) P `{∀ a, Persistent (P a)} :
  In np L →
  link_map_rep γz L P ⊢
               (∃ np', ((⌜ In np' L ⌝ ∗ P np') ∨ ⌜ np' = right_sentinel ⌝) ∗
                       node_next np ↦{1/2} (rep_to_node np') ∗
                       (∃ γ N, is_lock γ N (node_lock np)
                                       (∃ np'', node_next np ↦{1/2} rep_to_node np'' ∗
                                                 own γz (GSet (Zlt_range (node_key np)
                                                                         (node_key np''))))) ∗
                       P np ∗
                       (node_next np ↦{1/2} (rep_to_node np') -∗ link_map_rep γz L P)
               ).
Proof.
  induction L.
  - inversion 1.
  - intros [Hhd|Hrec].
    * subst. destruct L as [|np' L].
      ** iIntros "(?&#Hinv&#?&?)".
         iExists right_sentinel.
         iSplitL ""; first by auto.
         iFrame. iFrame "Hinv". auto.
      ** rewrite link_map_rep_unfold2.
         iIntros "(?&#Hinv&#?&Htl)".
         iPoseProof (link_map_rep_P_hd with "Htl") as "#HP".
         iExists np'.
         iSplitL "".
         { iLeft. iFrame "HP".  iPureIntro. clear. firstorder. }
         iFrame. iFrame "Hinv". auto.
    * iIntros "Hmap".
      iPoseProof (link_map_rep_cons_invert with "Hmap") as "(Hmap&Hclose)".
      iPoseProof (IHL Hrec with "Hmap") as "Hmap'".
      iDestruct "Hmap'" as (np') "(Hpure&Hpt&#Hinv&#HP&Hclose2)".
      iExists np'. iFrame.
      iSplitL "Hpure".
      { iDestruct "Hpure" as "[(Hpure&HP')|?]"; eauto. iLeft. iFrame.
        iDestruct "Hpure" as %Hpure. iPureIntro. clear -Hpure. firstorder. }
      iFrame "Hinv HP". iIntros "H". iApply "Hclose". iApply "Hclose2". auto.
Qed.
 
 Lemma link_map_rep_invert_split γz np_pred np_succ (L: list node_rep) L1 L2
       P `{∀ a, Persistent (P a)} :
  L = L1 ++ (np_pred :: np_succ :: L2) →
  link_map_rep γz L P ⊢ node_next np_pred ↦{1/2} (rep_to_node np_succ) ∗
                       (∃ γ N, is_lock γ N (node_lock np_pred)
                                       (∃ np'', node_next np_pred ↦{1/2} rep_to_node np'' ∗
                                                 own γz (GSet (Zlt_range (node_key np_pred)
                                                                         (node_key np''))))) ∗
                       P np_pred ∗
                       (node_next np_pred ↦{1/2} (rep_to_node np_succ) -∗ link_map_rep γz L P).
Proof.
  intros ->. induction L1.
  * rewrite cat0s.
    rewrite link_map_rep_unfold2.
    iIntros "(Hnext&#H1&#H2&?)".
    iFrame "#". iFrame. 
    auto.
  * rewrite cat_cons.
    iIntros "Hmap".
    iPoseProof (link_map_rep_cons_invert with "Hmap") as "(Hmap1&Hmap2)".
    iPoseProof (IHL1 with "Hmap1") as "(Hpt&#Hlock&#HP&Hrest)".
    iFrame "#". iFrame.
    iIntros "Hpt". iApply "Hmap2". iApply "Hrest". iFrame.
Qed.

Lemma link_map_rep_invert_split' γz np_pred np_succ (L: list node_rep) L1 L2
      P `{∀ a, Persistent (P a)} :
  L ++ [right_sentinel] = L1 ++ (np_pred :: np_succ :: L2) →
  link_map_rep γz L P ⊢ node_next np_pred ↦{1/2} (rep_to_node np_succ) ∗
                       (∃ γ N, is_lock γ N (node_lock np_pred)
                                       (∃ np'', node_next np_pred ↦{1/2} rep_to_node np'' ∗
                                                 own γz (GSet (Zlt_range (node_key np_pred)
                                                                         (node_key np''))))) ∗
                       P np_pred ∗
                       (node_next np_pred ↦{1/2} (rep_to_node np_succ) -∗ link_map_rep γz L P).
Proof.
  revert L. induction L1 => L Heq.
  * rewrite cat0s in Heq.
    destruct L as [| np' L].
    { exfalso.  rewrite //= in Heq; inversion Heq. }
    inversion Heq as [[Heq' Heq'']]. subst.
    destruct L as [| np'' L].
    ** rewrite //= in Heq''. inversion Heq''. subst.
       iIntros "(Hnext&#H1&#H2&?)".
       iFrame "#". iFrame. auto.
    ** inversion Heq''. subst.
       rewrite link_map_rep_unfold2.
       iIntros "(Hnext&#H1&#H2&?)".
       iFrame "#". iFrame. 
       auto.
  * destruct L as [| np' L].
    { exfalso. rewrite //= in Heq; inversion Heq as [[Heq' Heq'']].
      destruct L1 => //=; inversion Heq''. }
    inversion Heq as [[Heq' Heq'']]; subst. 
    iIntros "Hmap".
    iPoseProof (link_map_rep_cons_invert with "Hmap") as "(Hmap1&Hmap2)".
    iPoseProof (IHL1 with "Hmap1") as "(Hpt&#Hlock&#HP&Hrest)"; auto.
    iFrame "#". iFrame.
    iIntros "Hpt". iApply "Hmap2". iApply "Hrest". iFrame.
Qed.

Definition is_map_of_nset (S: gset node_rep) (Smap: gmap Z (agree node_rep)) :=
  (∀ nr, nr ∈ S → Smap !! (node_key nr) ≡ Some (to_agree nr))
  ∧ (∀ k nr, Smap !! k ≡ Some (to_agree nr) → node_key nr = k ∧ nr ∈ S).

                                     
Definition link_map_inv (γl1 γl2 γl3 γl4: gname) np P `{∀ a, Persistent (P a)} : iProp Σ :=
  (∃ S: gset node_rep, ∃ L: seq node_rep, ∃ Smap : gmap Z (agree node_rep),
          ⌜ Permutation L (elements S) ∧ Sorted (Zlt) (map node_key (np :: L ++ [right_sentinel]))
          ∧  is_map_of_nset S Smap⌝ ∗
        link_map_rep γl3 (np :: L) P ∗
        own γl1 (● S) ∗
        own γl2 (●! S) ∗
        own γl4 (● Smap)
  )%I.


(* We first give a spec for the case where one does not have complete ownership of the list...
   in this case little can be said about the number of comparisons performed. *)
Lemma findPred_spec1 N1 γl1 γl2 γl3 γl4 np_left P `{∀ a, Persistent (P a)} np k (Hlt_max: k < INT_MAX):
  {{{ inv N1 (link_map_inv γl1 γl2 γl3 γl4 np_left P) ∗
          (⌜ np = np_left ⌝ ∨ own γl1 (◯ {[ np ]})) ∗
          ⌜ node_key np < k ⌝ }}}
    findPred (rep_to_node np) #k
    {{{ (np': node_rep) (ck: Z) (cmps: Z), RET (rep_to_node np', (#ck, #cmps));
          (⌜ np' = np_left ⌝ ∨ own γl1 (◯ {[ np' ]})) ∗
          ⌜ node_key np' < k ⌝ ∗ P np' ∗ 
                             (∃ np'' γ N, is_lock γ N (node_lock np')
                                             (∃ np'', node_next np' ↦{1/2} rep_to_node np'' ∗
                                                 own γl3 (GSet (Zlt_range (node_key np')
                                                                         (node_key np'')))) ∗
                             ⌜ node_key np'' = ck ⌝ ∗
                              ((⌜ np'' = right_sentinel ⌝ ∨ (own γl1 (◯ {[ np'' ]}) ∗ P np''))))
    }}}.
Proof.
  iIntros (Φ) "(#Hinv&Hown&Hp) HΦ". 
  wp_let. wp_let. generalize 0 => cmps. wp_let.
  iRevert (np cmps) "Hown Hp".
  iLöb as "IH". iIntros (np cmps) "Hown". iIntros (Hlt).
  wp_let. wp_let.
  rewrite /nodeNext.
  wp_let. wp_proj. wp_proj.
  wp_bind (! #(node_next np))%E.
  iInv N1 as "H1" "Hclose".
  rewrite /link_map_inv.
  iDestruct "H1" as (S L Smap) "(H1a&Hlink&HownS1&HownS2)".
  iMod "H1a". iDestruct "H1a" as %(Hperm&Hsorted&Hnset).
  iMod "HownS1".
  iAssert ((⌜ In np (np_left :: L) ⌝)%I) with "[HownS1 Hown]" as %Hin.
  { 
    iDestruct "Hown" as "[%|Hown]".
    - iPureIntro. subst. by left.
    - iDestruct (own_valid_2 with "HownS1 Hown") as
        %[Hvalid%gset_included]%auth_valid_discrete_2.
      assert (np ∈ L) as Hin_L%elem_of_list_In.
      {  rewrite Hperm. clear -Hvalid. apply elem_of_elements. rewrite elem_of_subseteq in Hvalid *.
         set_solver+. }
      assert (Hin: In np (np_left :: L)).
      { by right. }
      done.
  }
  rewrite (link_map_rep_invert _ _ _ _ Hin).
  iDestruct "Hlink" as (np') "(Hnp_in&Hnext&Hlock&#HP&Hclose')".
  iMod "Hnext". wp_load.
  (* iDestruct "Hnp_in" as %Hnp_in. *)
  iMod (own_update with "HownS1") as "[HownS1 HownS1_dup]".
  { apply auth_update_alloc, (gset_local_update S _ S). reflexivity. }
  iMod ("Hclose" with "[HownS1 HownS2 Hclose' Hnext]") as "_".
  { iNext.  iExists S, L, Smap. iFrame. iSplitL ""; first by auto. iApply "Hclose'". auto. }
  iModIntro.
  wp_let. wp_let. wp_proj.
  wp_let. wp_op.
  case_bool_decide; wp_if.
  * wp_op. iApply "HΦ".
    iFrame "# ∗". iSplitL ""; auto.
    iExists np'.
    iDestruct "Hlock" as (γ N) "Hlock".
    iExists _, _; iFrame. iSplitL ""; auto.
    iDestruct "Hnp_in" as "[(Hnp_in&HP')|?]".
    *** iRight. iFrame.
        iDestruct "Hnp_in" as %Hnp_in.
        destruct Hnp_in as [Hnp_in|].
        { exfalso.
          edestruct (Sorted_lt_hd _ _ _ Hin); subst; try omega.
          eapply Sorted_nodekey_snoc; eauto.
        }
        assert (np' ∈ S).
        { apply elem_of_elements. rewrite -Hperm. apply elem_of_list_In. auto. }
        assert (S ≡ S ⋅ {[np']}) as ->.
        { rewrite gset_op_union //=. set_solver. }
        iDestruct "HownS1_dup" as "(H1&H2)".
        iFrame.
    *** by iLeft.
  * wp_op. wp_let. iApply ("IH" with "HΦ [HownS1_dup Hnp_in]").
    {
      iDestruct "Hnp_in" as "[(Hnp_in&?)|%]"; last first.
      { exfalso. cut (k > node_key np'); try omega. subst. rewrite /right_sentinel/node_key//=. 
        omega. }
      iDestruct "Hnp_in" as %Hnp_in.
      destruct Hnp_in.
      ** iLeft; auto. 
      ** iRight.
         assert (np' ∈ S).
         { apply elem_of_elements. rewrite -Hperm. apply elem_of_list_In. auto. }
         assert (S ≡ S ⋅ {[np']}) as ->.
         { rewrite gset_op_union //=. set_solver. }
         iDestruct "HownS1_dup" as "(H1&H2)".
         iFrame.
    }
    iPureIntro. omega.
Qed.


Arguments rep_to_node : simpl never.
Opaque rep_to_node.

Lemma findPred_aux_spec N1 γl1 γl2 γl3 γl4 np_left P `{∀ a, Persistent (P a)} np np_pred np_find cmps k
     S L Lvisited Lremain Lafter:
  Permutation (elements S) L →
  Sorted (Zlt) (map node_key (np_left :: L ++ [right_sentinel])) →
  k < INT_MAX →
  node_key np_find >= k →
  node_key np_pred < k →
  Lvisited ++ (np :: Lremain) ++ (np_find :: Lafter) = np_left :: L ++ [right_sentinel] →
  (∃ L1 L2, L1 ++ (np_pred :: np_find :: L2) = np_left :: L ++ [right_sentinel]) →
  {{{ inv N1 (link_map_inv γl1 γl2 γl3 γl4 np_left P) ∗
      own γl2 (◯! S) ∗
          (⌜ np = np_left  ∨ np ∈ S ⌝) ∗
          ⌜ node_key np < k ⌝ }}}
    findPred_aux #cmps (rep_to_node np) #k
    {{{ RET (rep_to_node np_pred, (# (node_key np_find), #(cmps + 1 + length Lremain)));
        own γl2 (◯! S) ∗
          P np_pred ∗ (∃ γ N, is_lock γ N (node_lock np_pred)
                                      (∃ np'', node_next np_pred ↦{1/2} rep_to_node np'' ∗
                                                         own γl3 (GSet (Zlt_range (node_key np_pred)
                                                                                  (node_key np'')))))
    }}}.
Proof.
  intros Hperm Hsorted Hlt_max Hfind_key Hpred_key Hsplit1 Hsplit2.
  iIntros (Φ) "(#Hinv&Hown&Hp) HΦ". 
  iRevert (np cmps Lvisited Lremain Hsplit1) "Hown Hp HΦ".
  iLöb as "IH". iIntros (np cmps Lvisited Lremain Hsplit1) "Hown Hp HΦ".
  wp_let. wp_let. wp_let.
  rewrite -fold_rep_to_node.
  rewrite /nodeNext.
  wp_let. wp_proj. wp_proj.
  wp_bind (! #(node_next np))%E.
  iInv N1 as "H1" "Hclose".
  rewrite /link_map_inv.
  iDestruct "H1" as (S' L' Smap') "(H1a&Hlink&HownS1&HownS2&HownSmap)".
  iMod "H1a". iDestruct "H1a" as %(Hperm'&Hsorted'&Hsmap).
  iMod "HownS2".
  iDestruct (own_valid_2 with "HownS2 Hown") as % ->%frac_auth_agreeL.
  assert (L = L') as <-.
  { eapply Sorted_nodekey_uniq.
    * rewrite //= map_cat in Hsorted.
      rewrite -cat_cons in Hsorted. apply Sorted_Zlt_app in Hsorted as (Hsorted&?).
      apply Sorted_inv in Hsorted. intuition. 
    * apply Sorted_nodekey_snoc, Sorted_inv in Hsorted'; intuition. 
    * rewrite -Hperm; by symmetry.
  }
  destruct Lremain as [|np' Lremain].
  * rewrite (link_map_rep_invert_split' _ np np_find (np_left :: L)); last first.
    { rewrite //= -Hsplit1 cat_cons //=. }
    iDestruct "Hlink" as "(Hpt&#His_lock&#HP&Hclose')".
    wp_load.
    iMod ("Hclose" with "[Hclose' Hpt HownS1 HownS2 HownSmap]").
    { iNext. iExists S, L, Smap'; iSplit; auto.
      iFrame. iApply "Hclose'". iFrame. }
    iModIntro. wp_let. wp_let.
    rewrite -fold_rep_to_node.
    rewrite (fold_rep_to_node). 
    repeat wp_proj.
    wp_let.  wp_op.
    case_bool_decide; last omega.
    wp_if. wp_op.
    rewrite //= Zplus_0_r.
    assert (np_pred = np) as ->.
    { destruct Hsplit2 as (L1&L2&Heq).  rewrite -Heq /= in Hsplit1.
      rewrite ?cat_cons //= in Hsplit1.
      apply NoDup_pred_unique in Hsplit1; eauto.
      rewrite Hsplit1 Heq.
      eapply NoDup_map_inv.
      rewrite -NoDup_ListNoDup. apply Sorted_Zlt_NoDup.
      rewrite -seq_ext.map_legacy; eauto.
    }
    iApply "HΦ".
    iDestruct "Hp" as "(Hp&?)". iFrame. iFrame "#".
  * rewrite (link_map_rep_invert_split' _ np np' (np_left :: L)); last first.
    { rewrite //= -Hsplit1 cat_cons //=. }
    iDestruct "Hlink" as "(Hpt&#His_lock&#HP&Hclose')".
    wp_load.
    iMod ("Hclose" with "[Hclose' Hpt HownS1 HownS2 HownSmap]").
    { iNext. iExists S, L, Smap'; iSplit; auto.
      iFrame. iApply "Hclose'". iFrame. }
    iModIntro. wp_let. wp_let.
    rewrite -fold_rep_to_node.
    rewrite (fold_rep_to_node). 
    repeat wp_proj.
    wp_let. wp_op. 
    case_bool_decide as Hcase.
    { exfalso.
      cut (node_key np' <= node_key np_pred); first by omega.
      assert (In np_pred (np' :: Lremain)) as Hin_np_pred.
      { destruct Hsplit2 as (L1&L2&Heq). 
        rewrite -Heq in Hsplit1.
        induction Lremain as [| np'' Lremain] using rev_ind.
        * rewrite //= in Hsplit1.
          left. eapply (NoDup_pred_unique (Lvisited ++ [:: np])); rewrite -catA //=.
          rewrite Hsplit1. rewrite Heq.
          eapply NoDup_map_inv.
          rewrite -NoDup_ListNoDup. apply Sorted_Zlt_NoDup.
          rewrite -seq_ext.map_legacy; eauto.
        *  right.  apply in_app_iff. right.
           rewrite //= in Hsplit1.
          rewrite -catA ?cat_cons in Hsplit1.
          left. eapply (NoDup_pred_unique (Lvisited ++ [:: np, np' & Lremain])); last first.
          { erewrite <-Hsplit1.
            rewrite -?catA; f_equal. }
          rewrite -catA.
          rewrite ?cat_cons //=.
          rewrite ?cat_cons //= in Hsplit1.
          rewrite Hsplit1  Heq.
          eapply NoDup_map_inv.
          rewrite -NoDup_ListNoDup. apply Sorted_Zlt_NoDup.
          rewrite -seq_ext.map_legacy; eauto.
      }
      cut (Sorted Zlt (map node_key (np' :: Lremain))).
      { intros Hsorted''. apply Sorted_StronglySorted in Hsorted''; last eauto with *.
        inversion Hsorted''; subst.  inversion Hin_np_pred; first by (subst; omega).
        apply Z.lt_le_incl. eapply Forall_forall; eauto.
        apply in_map_iff; eexists; eauto. }
     rewrite -Hsplit1 in Hsorted. 
      rewrite ?map_cat in Hsorted.
      apply Sorted_Zlt_app in Hsorted as (Hs1&Hs2).
      apply Sorted_Zlt_app in Hs2 as (Hs2&Hs3). inversion Hs2. auto.
    }
    wp_if. wp_op.
    iApply ("IH" $! np' (cmps + 1) (Lvisited ++ [:: np]) with "[] [$] []").
    { iPureIntro. rewrite //= -catA //=. rewrite -Hsplit1; eauto. }
    { iSplit; iPureIntro.
      * right. apply elem_of_elements. rewrite Hperm.
        destruct Lvisited.
        ** assert (np' ∈ L ++ [right_sentinel]) as Hin.
           { inversion Hsplit1; subst; by left. }
           apply elem_of_list_In, in_app_iff in Hin.
           destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
           subst. exfalso. rewrite /node_key/right_sentinel//= in Hcase; omega.
        ** assert (np' ∈ L ++ [right_sentinel]) as Hin.
           { inversion Hsplit1; subst.
             apply elem_of_list_In. apply in_app_iff.
             right. right; left. auto. }
           apply elem_of_list_In, in_app_iff in Hin.
           destruct Hin as [|[|[]]]; first by eapply elem_of_list_In.
           subst. exfalso. rewrite /node_key/right_sentinel//= in Hcase; omega.
      * omega.
    }
    iNext. replace (cmps + 1 + 1 + strings.length Lremain) with
               (cmps + 1 + length (np' :: Lremain)); last first.
    { rewrite /=. rewrite Zpos_P_of_succ_nat. omega. }
    iApply "HΦ".
Qed.

Lemma node_list_split_cover L np_left k:
  node_key np_left < k < INT_MAX →
  ∃ np_pred np_find L1 L2,
    node_key np_pred < k ∧ node_key np_find >= k ∧
    np_left :: L ++ [right_sentinel] = L1 ++ (np_pred :: np_find :: L2).
Proof.
  revert np_left.
  induction L as [| np L] => np_left.
  - intros (?&?). exists np_left, right_sentinel, [::], [::].
    split_and!; auto. rewrite /right_sentinel/node_key//=; eauto. omega.
  - intros (?&?).
    destruct (Z_lt_dec (node_key np) k).
    * edestruct IHL as (np_pred&np_find&L1&L2&Hlt&Hgt&Heq); eauto.
      exists np_pred, np_find, (np_left :: L1), L2.
      split_and!; eauto. rewrite //= Heq. auto.
    * exists np_left, np, [::], (L ++ [right_sentinel]).
      split_and!; eauto.
Qed.

Lemma node_list_split_cover' L L1 L2 np_left np_pred np_find k:
  Sorted Zlt (map node_key (np_left :: L ++ [right_sentinel])) →
  node_key np_left < k < INT_MAX →
  node_key np_pred < k → node_key np_find >= k  →
  np_left :: L ++ [right_sentinel] = L1 ++ (np_pred :: np_find :: L2) →
  (list_between (map node_key L) (node_key np_left) k = [::] ∧ L1 = [::]) ∨
  (∃ L1', L1 = np_left :: L1' ∧ list_between (map node_key L) (node_key np_left) k =
                                map node_key L1' ++ [node_key np_pred]).
Proof.
  intros Hsort Hrange1 Hrange2 Hrnage3 Heq. destruct L1.
  - rewrite //=. 
    inversion Heq as [[Heq' Heq'']]; subst.
    left. split; auto.
    apply list_between_all_ge.
    intros. apply Zle_ge.
    apply Sorted_StronglySorted in Hsort; last auto with *.
    rewrite Heq //= in Hsort.
    apply StronglySorted_inv in Hsort as (Hsort&Hforall1).
    apply StronglySorted_inv in Hsort as (Hsort&Hforall2).
    assert (Hin_i: In i (map node_key (np_find :: L2))).
    { rewrite -Heq''. rewrite map_cat. apply in_app_iff. by left. }
    rewrite //= in Hin_i.
    inversion Hin_i; subst.
    * omega.
    * apply Z.lt_le_incl.
      eapply (Z.le_lt_trans _ (node_key np_find)); first omega.
      eapply Forall_forall; eauto.
  - right. inversion Heq; subst. exists L1; split; auto.
    transitivity (list_between [seq node_key i | i <- (L ++ [:: right_sentinel])] (node_key n) k).
    { rewrite /list_between. 
      rewrite map_cat filter_cat //=.
      destruct Zbetween as [Hcase|].
      { replace (node_key right_sentinel) with INT_MAX in Hcase by
            (rewrite /node_key/right_sentinel//=). omega. }
      rewrite cats0 //=.
    }
    rewrite H1.
    rewrite /list_between map_cat ?map_cons filter_cat ?filter_cons.
    f_equal.
    * feed pose proof (list_between_all_in_range (map node_key L1) (node_key n) k) as Hlist.
      { intros i Hin. split.
        * apply Sorted_StronglySorted in Hsort; last eauto with *.
          { rewrite map_cons in Hsort. apply StronglySorted_inv in Hsort as (Hsort&Hforall).
            rewrite H1 in Hforall.
            eapply Forall_forall; eauto. rewrite map_cat. apply in_app_iff; by left.
          }
        * rewrite map_cons in Hsort. apply Sorted_inv in Hsort as (Hsort&Hforall).
          rewrite H1 in Hsort. rewrite map_cat in Hsort.
          transitivity (node_key np_pred); last auto.
          eapply Zlt_Sorted_forall_before; eauto.
      }
      rewrite /list_between in Hlist. rewrite Hlist. done.
    * rewrite //=. destruct Zbetween; try omega.
      ** destruct Zbetween; first omega.
         f_equal.
         feed pose proof (list_between_all_ge (map node_key L2) (node_key n) k) as Hlist.
         { intros i Hin. 
           apply Zle_ge.
           rewrite Heq in Hsort.
           rewrite map_cat in Hsort.
           apply Sorted_Zlt_app in Hsort as (Hs1&Hs2).
           apply Sorted_StronglySorted in Hs2; last auto with *.
           rewrite ?map_cons in Hs2.
           apply StronglySorted_inv in Hs2 as (Hs2&_).
           apply StronglySorted_inv in Hs2 as (Hs2&Hforall2).
           apply Z.lt_le_incl.
           eapply (Z.le_lt_trans _ (node_key np_find)); first omega.
           eapply Forall_forall; eauto.
         }
         rewrite /list_between in Hlist; rewrite Hlist //=.
      ** destruct Zbetween; first omega.
         exfalso.
         cut (node_key n < node_key np_pred); first omega.
         rewrite H1 in Hsort.
         apply Sorted_StronglySorted in Hsort; last auto with *.
         rewrite ?map_cons in Hsort.
         apply StronglySorted_inv in Hsort as (Hsort&Hforall).
         eapply Forall_forall; eauto. rewrite map_cat in_app_iff.
         right. by left.
Qed.

Transparent rep_to_node.

Lemma node_list_split_cover'' L Lvisited L' L1 L2 np_left np np_pred np_find k:
  Sorted Zlt (map node_key (np_left :: L ++ [right_sentinel])) →
  node_key np < k < INT_MAX →
  node_key np_pred < k → node_key np_find >= k  →
  np_left :: L = (Lvisited ++ (np :: L')) →
  np :: L' ++ [right_sentinel] = L1 ++ (np_pred :: np_find :: L2) →
  ∃ Lremain, Lvisited ++ (np :: Lremain) ++ np_find :: L2 = np_left :: L ++ [:: right_sentinel]
             ∧ length Lremain = length ((list_between (map node_key L) (node_key np) k))
             ∧ fold_left Z.max (list_between [seq node_key i | i <- L] (node_key np) k)
                         (node_key np) = node_key np_pred.
Proof.
  intros Hsort ??? Heq1 Heq2.
  feed pose proof (node_list_split_cover' L' L1 L2 np np_pred np_find k) as Hcase; auto.
  { rewrite -cat_cons Heq1 -catA in Hsort.
    rewrite ?map_cat in Hsort. apply Sorted_Zlt_app in Hsort as (Hs1&Hs2).
    rewrite -cat_cons map_cat //=. }
  assert (Hlb: list_between [seq node_key i | i <- L] (node_key np) k =
          list_between [seq node_key i | i <- L'] (node_key np) k).
  {
    destruct Lvisited.
    * inversion Heq1; subst.  done.
    * inversion Heq1; subst. rewrite map_cat.
      rewrite list_between_cat.
      rewrite list_between_all_le_ge //=.
      { destruct Zbetween; first omega. auto. }
      intros i Hin. left. apply Z.lt_le_incl.
      eapply (Zlt_Sorted_forall_before _ (map node_key (n :: Lvisited))
                                        (map node_key ((L' ++ [:: right_sentinel])))).
      { rewrite ?map_cons ?map_cat ?map_cons -?catA //= in Hsort *. }
        by right.
  }
  destruct Hcase as [(Hlb_nil&Heqnil)|(L1'&HeqL1&Hlb')].
  - exists [::].
    split_and!.
    * rewrite -?cat_cons Heq1 -catA. f_equal.
      rewrite ?cat_cons Heq2.
      rewrite Heqnil //=. rewrite Heqnil //= in Heq2. inversion Heq2; auto.
    * rewrite //=. subst. rewrite Hlb Hlb_nil //=. 
    * rewrite Hlb Hlb_nil //=.
      subst. inversion Heq2; auto.
  - exists (L1' ++ [np_pred]).
    split_and!.
    * rewrite -?cat_cons Heq1 -?catA. f_equal.
      rewrite ?cat_cons Heq2.
      rewrite HeqL1 //=.
    * rewrite Hlb Hlb' ?app_length //= map_length //=.
    * rewrite Hlb Hlb'.
      apply (fold_left_Sorted_Zmax _ _ _ [::]).
      rewrite -cat_cons Heq1 in Hsort.
      rewrite -catA map_cat in Hsort.
      apply Sorted_Zlt_app in Hsort as (Hs1&Hs2).
      rewrite cat_cons Heq2 in Hs2.
      replace (L1 ++ [:: np_pred, np_find & L2]) with
          ((L1 ++ [np_pred]) ++ (np_find :: L2)) in Hs2; last first.
      { rewrite -catA //=. }
      rewrite map_cat in Hs2.
      apply Sorted_Zlt_app in Hs2 as (Hs2&_).
      rewrite HeqL1 map_cons ?map_cat //= in Hs2.
Qed.

Lemma findPred_aux_spec2 N1 γl1 γl2 γl3 γl4 np_left P `{∀ a, Persistent (P a)} np k
     S:
  (*
  Permutation (elements S) L →
  Sorted (Zlt) (map node_key (np_left :: L ++ [right_sentinel])) →
   *)
  INT_MIN < k < INT_MAX →
  node_key np < k →
  {{{ inv N1 (link_map_inv γl1 γl2 γl3 γl4 np_left P) ∗
      own γl2 (◯! S) ∗
      (⌜ np = np_left  ∨ np ∈ S ⌝) ∗
      ⌜ node_key np < k ⌝ }}}
    findPred_aux #0 (rep_to_node np) #k
    {{{ (np': node_rep) (ck: Z) (cmps: Z), RET (rep_to_node np', (#ck, #cmps));
        own γl2 (◯! S) ∗ P np'
            ∗ (⌜ node_key np' = fold_left Zmax
                                          (list_between (map node_key (elements S)) (node_key np) k)
                                          (node_key np)
               ∧ node_key np' < k 
               ∧ (cmps = (1 + (length (list_between (map node_key (elements S)) (node_key np) k)))%nat)
               ∧ (k ∈ map node_key (elements S) ↔ ck = k)
               ∧ In np' (np_left :: elements S)⌝)
            ∗ (∃ γ N, is_lock γ N (node_lock np')
                                      (∃ np'', node_next np' ↦{1/2} rep_to_node np'' ∗
                                                         own γl3 (GSet (Zlt_range (node_key np')
                                                                                  (node_key np'')))))
    }}}.
Proof.
  iIntros (Hrange Hgt_left Φ) "(#Hinv&Hown&Hcase&Hlt) HΦ".
  iApply fupd_wp.
  iInv N1 as "Hinv'" "Hclose".
  iDestruct "Hinv'" as (S' L Smap) "(Hperm&Hrep&HownS1&HownS2&HownSmap)".
  iMod "Hperm". iDestruct "Hperm" as %(Hperm&Hsort&HSmap).
  iMod "HownS2".
  iDestruct (own_valid_2 with "HownS2 Hown") as % ->%frac_auth_agreeL.
  iMod ("Hclose" with "[Hrep HownS1 HownS2 HownSmap]").
  { iNext. iExists S, L, Smap. iFrame. auto. }
  iModIntro.
  symmetry in Hperm.
  
  destruct Hrange.
  iDestruct "Hcase" as %Hcase.
  iDestruct "Hlt" as %Hlt_np.
  edestruct (in_split np (np_left :: L)) as (Lvisited&L'&Heq_visited).
  { destruct Hcase; first by left.
    right. apply elem_of_list_In. rewrite - Hperm. apply elem_of_elements; auto. }
  edestruct (node_list_split_cover L' np k) as (np_pred&np_find&L1&L2&?&?&Heq_pred).
  { split; omega. }

  feed pose proof (node_list_split_cover'' L Lvisited L' L1 L2 np_left np np_pred np_find k)
    as Hcase_cover; eauto.
  destruct Hcase_cover as (Lremain&HL).

  wp_apply ((findPred_aux_spec N1 γl1 γl2 γl3 γl4 np_left P np np_pred np_find 0 k
              S L Lvisited)  with "[Hown]").
  { eassumption. }
  { eauto. }
  { auto. }
  { auto. }
  { auto. }
  { destruct HL as (HL&?). apply HL. }
  { exists (Lvisited ++ L1), L2.
    rewrite -catA -Heq_pred .
    rewrite -?cat_cons Heq_visited //= -?app_cat //= -?catA -?cat_cons //=.
  }
  iFrame. iFrame "Hinv". iSplit; auto.
  iIntros "(Hown&HP&Hlock)". iApply "HΦ". 
  iFrame. 

  destruct HL as (HLeq&Hlen&Hfold).
  iPureIntro. split_and!.
  - rewrite -Hfold. rewrite Hperm. done.
  - done. 
  - rewrite Hlen.
    rewrite Nat2Z.inj_add => //=.
    rewrite Z.add_0_l.
    rewrite Hperm. done.
  - rewrite Hperm.
    intros.
    split.
    * intros. eapply (Sorted_Zlt_cover_gap (map node_key (Lvisited ++ L1))
                                   (map node_key L2) (node_key np_pred)); auto.
      {
        rewrite -cat_cons Heq_visited in Hsort.
        rewrite -app_cat in Hsort.
        rewrite -catA cat_cons Heq_pred map_cat in Hsort.
        rewrite ?map_cat ?map_cons catA //= in Hsort *.
      }
      cut (In k (map (node_key) ((np_left :: L) ++ [right_sentinel]))).
      { intros Hin. rewrite Heq_visited in Hin.
        rewrite -app_cat -?catA cat_cons Heq_pred ?map_cat ?map_cons in Hin.
        rewrite ?map_cat -?catA //=. }
      rewrite map_cat. apply in_app_iff. left.
      right. auto. apply elem_of_list_In; auto.
    * intros. apply elem_of_list_In. apply in_map_iff. exists np_find; split; auto.
      cut (In np_find L').
      { destruct Lvisited; inversion Heq_visited; subst; auto.
        intros. rewrite in_app_iff. right. right. done.
      }
      cut (In np_find (L' ++ [right_sentinel])).
      { rewrite /right_sentinel.
        rewrite ?in_app_iff. intros [|[|[]]]; auto; subst; first by rewrite //= in H1.
      }
      destruct L1.
      ** rewrite //= in Heq_pred. inversion Heq_pred as [[Heq' Heq'']]; subst.
         rewrite Heq''. by left.
      ** inversion Heq_pred as [[Heq' Heq'']]; subst. rewrite Heq''.
         rewrite in_app_iff. right. right. left. auto.
  - rewrite Hperm. rewrite Heq_visited.
    cut (In np_pred (np :: L' ++ [:: right_sentinel])).
    { rewrite -cat_cons ?in_app_iff.
      intros [Hin|Hsent]%in_app_iff.
      * by right.
      * exfalso. inversion Hsent as [|[]]; subst.
        assert (node_key right_sentinel = INT_MAX) by (rewrite /node_key/right_sentinel//=).
        omega.
    }
    rewrite Heq_pred in_app_iff. right. by left.
Qed.
  
Lemma findLockPred_spec N1 γl1 γl2 γl3 γl4 np_left P
      `{∀ a, Persistent (P a)} np k (Hlt_max: k < INT_MAX):
  {{{ inv N1 (link_map_inv γl1 γl2 γl3 γl4 np_left P) ∗
          (⌜ np = np_left ⌝ ∨ own γl1 (◯ {[ np ]})) ∗
          ⌜ node_key np < k ⌝ }}}
    findLockPred (rep_to_node np) #k
    {{{ (np': node_rep) (ck: Z), RET (rep_to_node np', #ck);
          (⌜ np' = np_left ⌝ ∨ own γl1 (◯ {[ np' ]})) ∗
          ⌜ node_key np' < k ∧ k <= ck⌝ ∗ P np' ∗ 
          (∃ np'' γ N, is_lock N γ (node_lock np') (∃ np'', node_next np' ↦{1/2} rep_to_node np'' ∗
                                                            own γl3 (GSet (Zlt_range (node_key np')
                                                                         (node_key np''))))
                              ∗ locked γ
                              ∗ node_next np' ↦{1/2} rep_to_node np''
                              ∗ own γl3 (GSet (Zlt_range (node_key np') (node_key np''))) ∗
                              ⌜ node_key np'' = ck ⌝ ∗
                              ((⌜ np'' = right_sentinel ⌝ ∨ (own γl1 (◯ {[ np'' ]}) ∗ P np'')))
         )
    }}}.
Proof.
  iIntros (Φ) "(#Hinv&Hown&Hp) HΦ". 
  iRevert (np) "Hown Hp".
  iLöb as "IH". iIntros (np) "#Hown". iIntros (Hlt).
  wp_let. wp_let.
  rewrite /nodeNext.
  wp_let. wp_proj. wp_proj.
  wp_bind (! #(node_next np))%E.
  iInv N1 as "H1" "Hclose".
  rewrite /link_map_inv.
  iDestruct "H1" as (S L Smap) "(H1a&Hlink&HownS1&HownS2&HownSmap)".
  iMod "H1a". iDestruct "H1a" as %(Hperm&Hsorted&HSmap).
  iMod "HownS1".
  iAssert ((⌜ In np (np_left :: L) ⌝)%I) with "[HownS1 Hown]" as %Hin.
  { 
    iDestruct "Hown" as "[%|Hown]".
    - iPureIntro. subst. by left.
    - iDestruct (own_valid_2 with "HownS1 Hown") as
        %[Hvalid%gset_included]%auth_valid_discrete_2.
      assert (np ∈ L) as Hin_L%elem_of_list_In.
      {  rewrite Hperm. clear -Hvalid. apply elem_of_elements. rewrite elem_of_subseteq in Hvalid *.
         set_solver+. }
      assert (Hin: In np (np_left :: L)).
      { by right. }
      done.
  }
  rewrite (link_map_rep_invert _ _ _ _ Hin).
  iDestruct "Hlink" as (np') "(Hnp_in&Hnext&Hlock&#HP&Hclose')".
  iMod "Hnext". wp_load.
  (* iDestruct "Hnp_in" as %Hnp_in. *)
  iMod (own_update with "HownS1") as "[HownS1 HownS1_dup]".
  { apply auth_update_alloc, (gset_local_update S _ S). reflexivity. }
  iMod ("Hclose" with "[HownS1 HownS2 HownSmap Hclose' Hnext]") as "_".
  { iNext.  iExists S, L, Smap. iFrame. iSplitL ""; first by auto. iApply "Hclose'". auto. }
  iModIntro.
  wp_let. wp_let. wp_proj. 
  wp_let. wp_op.
  case_bool_decide; wp_if.
  * wp_let. repeat wp_proj.
    wp_bind (acquire _).
    iDestruct "Hlock" as (γ N) "#Hlock".
    iApply (acquire_spec with "Hlock").
    iNext. iIntros "(Hlocked&Hpt)".
    iDestruct "Hpt" as (np'') "(Hpt&Htok)".
    wp_let. wp_let. repeat wp_proj. wp_load.
    wp_let. wp_op. case_bool_decide; wp_if.
    ** iApply "HΦ". 
       iFrame "Hown HP". iSplitL ""; first by auto.
       iExists _, _, _. iFrame "Hlock Hpt Hlocked Htok".
       iSplitL ""; first by (iPureIntro; congruence).
       assert (np' = np'') as ->.
       { apply rep_to_node_inj; eauto. }
       iDestruct "Hnp_in" as "[(Hnp_in&HP')|?]".
       *** iRight. iFrame.
           iDestruct "Hnp_in" as %Hnp_in.
           destruct Hnp_in as [Hnp_in|].
           { exfalso. apply Sorted_nodekey_snoc in Hsorted.
             edestruct (Sorted_lt_hd _ _ _ Hin Hsorted); subst; omega. }
           assert (np'' ∈ S).
           { apply elem_of_elements. rewrite -Hperm. apply elem_of_list_In. auto. }
           assert (S ≡ S ⋅ {[np'']}) as ->.
           { rewrite gset_op_union //=. set_solver. }
           iDestruct "HownS1_dup" as "(H1&H2)".
           iFrame.
       *** by iLeft.
    ** wp_let. repeat wp_proj. wp_apply (release_spec with "[Hpt Hlocked Htok]").
       { iFrame "Hlock". iFrame. iExists _. iFrame. }
       iIntros. wp_let.
        iApply ("IH" with "HΦ [HownS1_dup]"); auto.
  * iApply ("IH" with "HΦ [HownS1_dup Hnp_in]").
    {
      iDestruct "Hnp_in" as "[(Hnp_in&HP')|%]"; last first.
      { exfalso. cut (k > node_key np'); try omega. subst. rewrite /right_sentinel/node_key//=. 
        omega. }
      iDestruct "Hnp_in" as %Hnp_in.
      destruct Hnp_in.
      ** iLeft; auto. 
      ** iRight.
         assert (np' ∈ S).
         { apply elem_of_elements. rewrite -Hperm. apply elem_of_list_In. auto. }
         assert (S ≡ S ⋅ {[np']}) as ->.
         { rewrite gset_op_union //=. set_solver. }
         iDestruct "HownS1_dup" as "(H1&H2)".
         iFrame.
    }
    iPureIntro. omega.
Qed.

Lemma link_map_rep_invert_to_insert N γz γ np np_succ np_new np_hd (L: list node_rep)
      P `{∀ a, Persistent (P a)} (Hsort: Sorted (Zlt) (map node_key (np_hd :: L ++ [right_sentinel])))
      (Hlt_sent: node_key np_new < node_key right_sentinel)
      (Hlt1: node_key np < node_key np_new) (Hlt2: node_key np_new < node_key np_succ):
  In np (np_hd :: L) → ∃ L', 
  (link_map_rep γz (np_hd :: L) P ∗ node_next np ↦{1/2} rep_to_node np_succ ∗ P np_new 
             ∗ node_next np_new ↦{1/2} rep_to_node np_succ ∗
             is_lock N γ (node_lock np_new)
                         (∃ np''0 : node_rep, node_next np_new ↦{1 / 2} rep_to_node np''0
                             ∗ own γz (GSet (Zlt_range (node_key np_new) (node_key np''0))))
                ⊢ node_next np ↦ rep_to_node np_succ ∗
                ⌜ Sorted Zlt (map node_key (np_hd :: L' ++ [right_sentinel])) ∧
                 Permutation (np_hd :: L') (np_hd :: np_new :: L) ⌝ ∗
                (node_next np ↦{1/2} (rep_to_node np_new) -∗ link_map_rep γz (np_hd :: L') P)).
Proof.
  remember (np_hd :: L) as L' eqn:HeqL'.
  revert np_hd L HeqL' Hsort.
  induction L' as [|np0]; first by inversion 1.
  intros np_hd L HeqL' Hsort. subst.
  inversion HeqL'; subst.
  inversion 1.
  * subst.
    exists (np_new :: L).
    iIntros "(Hlrep&Hnp_next&HP&Hnp_new_next&His_lock)".
    destruct L as [|].
    ** rewrite //=. 
       iDestruct "Hlrep" as "(Hnp_next'&?&?&?)".
       iDestruct (@mapsto_agree with "Hnp_next' Hnp_next") as %<-.
       iFrame.
       iSplitL "".
       { iPureIntro; split.
         * apply Sorted_cons; first repeat econstructor.
           auto.
           auto.
         * econstructor. done.
       }
       iFrame.
       iIntros "Hnext'". iFrame. 
       iExists _, _; iFrame "His_lock".
    ** rewrite link_map_rep_unfold2.
       iDestruct "Hlrep" as "(Hnp_next'&Hlock&HP_np&Hlrep)".
       iDestruct (@mapsto_agree with "Hnp_next' Hnp_next") as %Heq.
       apply rep_to_node_inj in Heq. subst.
       iFrame.
       iSplitL "".
       { iPureIntro; split.
         * rewrite ?map_cons in Hsort *.
           apply Sorted_inv in Hsort as (Hsort&?).
           apply Sorted_inv in Hsort as (Hsort&?); auto.
         * econstructor. auto.
       }
       iIntros "Hnext". iFrame. iExists N, γ; auto.
  * destruct L as [|np_hd2 L]; first by inversion H1.
    edestruct IHL' as (L'&HL').
    { eauto. }
    { apply Sorted_inv in Hsort; intuition. }
    { auto. }
    exists (np_hd2 :: L').
    iIntros "(Hlrep&Hnp_next&HP&Hnp_new_next&His_lock)".
    rewrite link_map_rep_unfold2.
    iDestruct "Hlrep" as "(Hnp_next'&Hlock&HP_np&Hlrep)".
    iPoseProof (HL' with "[$]") as "(Hpt&Hpure&Hclose)".
    iDestruct "Hpure" as %(Hsorted&Hperm).
    iFrame "Hpt".
    iSplitL "".
    { iPureIntro. split.
      ** rewrite ?map_cons in Hsort *.
         apply Sorted_cons; auto.
         econstructor.  apply Sorted_inv in Hsort as (?&Hhd).
         inversion Hhd. eauto.
      ** rewrite Hperm. econstructor. econstructor. 
    }
    iIntros "Hmap".
    rewrite link_map_rep_unfold2. iFrame.
    iApply "Hclose". done.
Qed.

Lemma link_map_rep_invert_to_insert' N γz γ np np_succ np_new np_hd (L: list node_rep)
      P `{∀ a, Persistent (P a)} (Hsort: Sorted (Zlt) (map node_key (np_hd :: L ++ [right_sentinel])))
      (Hlt_sent: node_key np_new < node_key right_sentinel)
      (Hlt1: node_key np < node_key np_new) (Hlt2: node_key np_new < node_key np_succ):
  In np (np_hd :: L) → ∃ L', 
    (link_map_rep γz (np_hd :: L) P ⊢
        (node_next np ↦{1/2} rep_to_node np_succ ∗ P np_new  ∗
                   node_next np_new ↦{1/2} rep_to_node np_succ ∗
                   is_lock N γ (node_lock np_new)
                         (∃ np''0 : node_rep, node_next np_new ↦{1 / 2} rep_to_node np''0
                             ∗ own γz (GSet (Zlt_range (node_key np_new) (node_key np''0)))) -∗
                (node_next np ↦ rep_to_node np_succ ∗
                 ⌜ Sorted Zlt (map node_key (np_hd :: L' ++ [right_sentinel])) ∧
                 Permutation (np_hd :: L') (np_hd :: np_new :: L) ⌝ ∗
                (node_next np ↦{1/2} (rep_to_node np_new) -∗ link_map_rep γz (np_hd :: L') P)))).
Proof.
  intros.
  edestruct (link_map_rep_invert_to_insert N γz γ np np_succ np_new np_hd L) as (L'&HL'); eauto.
  exists L'. iIntros.
  iPoseProof (HL' with "[$]") as "HL'".
  done.
Qed.

Opaque rep_to_node.

Lemma is_map_of_nset_insert S Smap np_new:
  is_map_of_nset S Smap →
  Smap !! (node_key np_new) = None →
  is_map_of_nset (S ∪ {[np_new]}) (<[node_key np_new := to_agree np_new]> Smap).
Proof.
  intros (Hmap1&Hmap2) Hnin.
  split.
  - intros nr. intros [HinS|Hin]%elem_of_union.
    * specialize (Hmap1 nr HinS).
      rewrite lookup_insert_ne; eauto.
      intros Heq. rewrite Heq in Hnin. rewrite Hnin in Hmap1. inversion Hmap1.
    * apply elem_of_singleton in Hin; subst. 
      rewrite lookup_insert; eauto.
  - intros k nr Heq.
    destruct (Z_eq_dec k (node_key np_new)).
    * subst. rewrite lookup_insert in Heq.
      apply Some_equiv_inj, to_agree_inj in Heq.
      rewrite leibniz_equiv_iff in Heq * => ->.
      split; auto.
      apply elem_of_union_r, elem_of_singleton; auto.
    * rewrite lookup_insert_ne in Heq; eauto. edestruct Hmap2; eauto; split; eauto.
      apply elem_of_union_l; auto.
Qed.

Lemma link_map_insert_spec N Nl γl1 γl2 γl3 γl4 np_left P `{∀ a, Persistent (P a)} np np_succ np_new
      γlnp_new S Smap q (Hlt_right: node_key np_new < node_key right_sentinel)
      (Hlt1: node_key np < node_key np_new) (Hlt2: node_key np_new < node_key np_succ)
      (HSmap: is_map_of_nset S Smap):
  {{{ inv N (link_map_inv γl1 γl2 γl3 γl4 np_left P) ∗
          own γl2 (◯!{q} S) ∗
          own γl4 (◯ Smap) ∗
          node_next np ↦{1/2} rep_to_node np_succ ∗
          (⌜ np = np_left ⌝ ∨ own γl1 (◯ {[np]})) ∗
          (node_next np_new ↦{1/2} rep_to_node np_succ) ∗
          is_lock Nl γlnp_new (node_lock np_new)
             (∃ np''0 : node_rep, node_next np_new ↦{1 / 2} rep_to_node np''0
             ∗ own γl3 (GSet (Zlt_range (node_key np_new) (node_key np''0)))) ∗
          P np_new  }}}
    (nodeNext (rep_to_node np) <- rep_to_node np_new)
    {{{ RET #(); own γl2 (◯!{q} (S ∪ {[ np_new ]})) ∗
                 own γl4 (◯ (<[node_key np_new := to_agree np_new]>Smap)) ∗ own γl1 (◯{[np_new]}) ∗
                 ⌜ is_map_of_nset (S ∪ {[ np_new ]}) (<[node_key np_new := to_agree np_new]>Smap) ⌝ ∗
                         node_next np ↦{1/2} rep_to_node np_new }}}.
Proof.
  iIntros (Φ) "(#Hinv&HownS&HownSmap&Hnp_next&Hnp_in&Hnp_new_next&#His_lock&HP) Hclose".
  wp_let. rewrite -fold_rep_to_node. do 2 wp_proj.
  iInv N as "Hlink_map" "Hclose_inv".
  iDestruct "Hlink_map" as (S' L Smap') "(H1a&Hlink&HownS1&HownS2&HownSmap')".
  iMod "H1a".
  iDestruct "H1a" as %(Hperm&Hsorted&HSmap').
  iMod "HownS1". iMod "HownS2".
  iAssert ((⌜ In np (np_left :: L) ⌝)%I) with "[HownS1 Hnp_in]" as %Hin.
  { 
    iDestruct "Hnp_in" as "[%|Hown]".
    - iPureIntro. subst. by left.
    - iDestruct (own_valid_2 with "HownS1 Hown") as
          %[Hvalid%gset_included]%auth_valid_discrete_2.
      assert (np ∈ L) as Hin_L%elem_of_list_In.
      { rewrite Hperm. clear -Hvalid. apply elem_of_elements. rewrite elem_of_subseteq in Hvalid *.
         set_solver+. }
      iPureIntro; by right.
  }
  rename Hsorted into Hsorted0.
  specialize (Sorted_nodekey_snoc _ _ _ Hsorted0) as Hsorted.
  edestruct (link_map_rep_invert_to_insert' Nl γl3 γlnp_new np np_succ np_new) as (L'&HL'); eauto.
  rewrite HL'.
  iDestruct ("Hlink" with "[$]") as "(>Hnext&Hpure&Hclose_rep)".
  wp_store.
  iDestruct "Hpure" as %(Hsorted'&Hperm').
  assert (HpermL': L' ≡ₚ elements {| mapset_car := map_of_list [seq (x, ()) | x <- L'] |}).
  { 
    apply elements_map_of_list.
    apply (NoDup_fmap_1 (node_key)).
    rewrite stdpp_ext.list_fmap_map.
    rewrite -map_legacy.
    apply Sorted_Zlt_NoDup. rewrite ?map_cons in Hsorted'.
    apply Sorted_inv in Hsorted' as (Hs1&?).
    eapply Sorted_nodekey_snoc' in Hs1.
    intuition. 
  }
  assert (Hequiv_S': S' ∪ {[ np_new ]} ≡ {| mapset_car := map_of_list [seq (x, ()) | x <- L'] |}).
  {
    intros x; split.
    - intros Hinx.
      apply elem_of_elements. rewrite -HpermL'.
      assert (Permutation L' (np_new :: L)) as ->.
      { apply Permutation.Permutation_cons_inv in Hperm'. auto. }
      apply elem_of_union in Hinx as [Hinx|Hin_new].
      * apply elem_of_elements in Hinx. rewrite -Hperm in Hinx * => Hinx.
        right. done.
      * set_solver.
    - rewrite -elem_of_elements. rewrite -HpermL'. 
      assert (Permutation L' (np_new :: L)) as ->.
      { apply Permutation.Permutation_cons_inv in Hperm'. auto. }
      inversion 1.
      * set_solver+. 
      * subst. apply elem_of_union_l.  apply elem_of_elements. rewrite -Hperm //.
  }

  iDestruct (own_valid_2 with "HownSmap' HownSmap") as %[HsubSmap Hval]%auth_valid_discrete_2.
  assert (Hnew_notin: Smap' !! node_key np_new = None).
  {
    destruct (Smap' !! node_key np_new) as [e|] eqn:Heq; last eauto.
    edestruct (to_agree_uninj e) as (nr&Heq_nr).
    { specialize (Hval (node_key np_new)).  rewrite Heq //= in Hval. }
    destruct HSmap' as (HSmap1&HSmap2).
    specialize (HSmap2 (node_key np_new) nr) as (Hkeygood&HinS'); eauto.
    { rewrite Heq_nr.  rewrite Heq. auto. }
    apply elem_of_elements in HinS'. rewrite -Hperm in HinS' * => HinL.
    apply Sorted_nodekey_snoc in Hsorted'.
    apply Sorted_Zlt_NoDup in Hsorted'. rewrite Hperm' in Hsorted' * => Hsorted'.
    rewrite ?map_cons in Hsorted'.
    apply NoDup_cons_12 in Hsorted'.
    apply NoDup_cons_11 in Hsorted'.
    exfalso. apply Hsorted'.
    rewrite -Hkeygood.
    apply elem_of_list_In. eapply in_map_iff; eexists; split; eauto.
    apply elem_of_list_In; eauto.
  }


  iDestruct (own_valid_2 with "HownS2 HownS") as %HsubS%frac_auth_included_total. 
  apply gset_included in HsubS.
  iMod (own_update_2 with "HownS2 HownS") as "[HownS2 HownS2_local]".
  { apply frac_auth_update, (gset_local_update_union _ _ {[ np_new ]}). }
  iMod (own_update with "HownS1") as "[HownS1 HownS1_local]".
  { apply auth_update_alloc, (gset_local_update_union _ _ {[ np_new ]}). } 
  iMod (own_update_2 with "HownSmap' HownSmap") as "[HownSmap' HownSmap]".
  { apply auth_update. apply (alloc_local_update _ _ (node_key np_new) (to_agree np_new)); eauto.
    rewrite //=. }
  iDestruct "Hnext" as "(Hnext1&Hnext2)".
  iMod ("Hclose_inv" with "[HownS1 HownS2 Hclose_rep Hnext2 HownSmap']").
  { 
    iNext. rewrite /link_map_inv.
    iExists _, L', (<[node_key np_new := to_agree np_new]>Smap'); iFrame.
    iSplitL "".
    * iPureIntro. split_and!; auto.
      ** rewrite Hequiv_S'. done.
      ** apply is_map_of_nset_insert; eauto.
    * iApply "Hclose_rep". iFrame.
  }
  iModIntro. iApply "Hclose".
  rewrite left_id. iFrame.
  iPureIntro. apply is_map_of_nset_insert; eauto.
  eapply dom_included in HsubSmap.
  cut (¬ node_key np_new ∈ dom (gset Z) Smap).
  { rewrite not_elem_of_dom => //=. }
  cut (¬ node_key np_new ∈ dom (gset Z) Smap').
  { clear -HsubSmap. set_solver. }
  rewrite not_elem_of_dom; eauto.
Qed.

Definition skiplist_prob_inv (γst γsb1 γsb2 γs_tok : gname) S : iProp Σ :=
  (∃ St Sb: gset Z,
      ⌜ St ⊆ Sb ⌝ ∗
      own γst (●! St) ∗
      own γsb1 (● Sb) ∗
      own γsb2 (●! Sb) ∗
      own γs_tok (GSet Sb) ∗
      (own γsb2 (◯! Sb) ∨
       ownProb (skiplist (elements (S ∖ Sb)) (elements St) (elements Sb))))%I.

Lemma new_spec Nt Nb Ns S:
  {{{ ownProb (skiplist (elements S) [::] [::]) }}}
    newSkipList #()
    {{{ γt1 γt2 γt3 γt4 γb1 γb2 γb3 γb4 γst γsb1 γsb2 np_left_top np_left_bottom,
        RET (rep_to_node np_left_top);
      ⌜ node_key (np_left_top) = INT_MIN ⌝ ∗
      ⌜ node_key (np_left_bottom) = INT_MIN ⌝ ∗
      inv Nt (link_map_inv γt1 γt2 γt3 γt4 np_left_top
                           (λ np, ∃ np', ⌜ node_val np = rep_to_node np' ∧
                                           node_key np = node_key np' ⌝ ∗
                                           (⌜ np' = np_left_bottom ⌝ ∨
                                            (own γb1 (◯ {[ np' ]}) ∗ own γsb1 (◯ {[ node_key np' ]})
             )))) ∗
      inv Nb (link_map_inv γb1 γb2 γb3 γb4 np_left_bottom
                               (λ np', ⌜ np' = np_left_bottom ⌝ ∨
                                        own γsb1 (◯ {[ node_key np' ]}))%I) ∗
      inv Ns (skiplist_prob_inv γst γsb1 γsb2 γb3 S) ∗
      own γt2 (◯! (∅ : gset node_rep)) ∗
      own γt4 (◯ (∅ : gmap Z (agree node_rep))) ∗
      own γb2 (◯! (∅ : gset node_rep)) ∗
      own γb4 (◯ (∅ : gmap Z (agree node_rep))) ∗
      own γst (◯! (∅ : gset Z)) ∗
      own γsb2 (◯! (∅ : gset Z)) }}}.
Proof.
  iIntros (Φ) "Hown HΦ".
  iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
    as (γt1) "[HownT1 HownT1']"; first (apply auth_valid_discrete_2; split; done).
  iMod (own_alloc (●! (∅ : gset node_rep) ⋅ ◯! (∅: gset node_rep)))
    as (γt2) "[HownT2 HownT2']"; first done.
  iMod (own_alloc (GSet (Zlt_range INT_MIN INT_MAX)))
    as (γt3) "HownT3"; first done.
  iMod (own_alloc (● (∅ : gmap Z (agree node_rep)) ⋅ ◯ (∅: gmap Z (agree node_rep))))
    as (γt4) "[HownT4 HownT4']"; first (apply auth_valid_discrete_2; split; done).

  iMod (own_alloc (● (∅ : gset node_rep) ⋅ ◯ (∅: gset node_rep)))
    as (γb1) "[HownB1 HownB1']"; first (apply auth_valid_discrete_2; split; done).
  iMod (own_alloc (●! (∅ : gset node_rep) ⋅ ◯! (∅: gset node_rep)))
    as (γb2) "[HownB2 HownB2']"; first done.
  iMod (own_alloc (GSet (Zlt_range INT_MIN INT_MAX)))
    as (γb3) "HownB3"; first done.
  iMod (own_alloc (● (∅ : gmap Z (agree node_rep)) ⋅ ◯ (∅: gmap Z (agree node_rep))))
    as (γb4) "[HownB4 HownB4']"; first (apply auth_valid_discrete_2; split; done).

  assert (is_map_of_nset ∅ ∅).
  { split; intros nr Hin.
    - inversion Hin.
    - destruct (∅ !! nr) eqn:Heq; auto.
      * inversion Heq. 
      * inversion 1.
  }

  assert (GSet (Zlt_range INT_MIN INT_MAX) ≡
          GSet (Zlt_range INT_MIN INT_MAX) ⋅ GSet (∅)) as ->.
  { rewrite gset_disj_union; last by set_solver.
    f_equal. set_solver. }
  iDestruct "HownB3" as "(HownB3&Hemp)".
    
  iMod (own_alloc (●! (∅ : gset Z) ⋅ ◯! (∅: gset Z)))
    as (γst) "[HownST HownST']"; first done.
  iMod (own_alloc (● (∅ : gset Z) ⋅ ◯ (∅: gset Z)))
    as (γsb1) "[HownSB1 HownSB1']"; first (apply auth_valid_discrete_2; split; done).
  iMod (own_alloc (●! (∅ : gset Z) ⋅ ◯! (∅: gset Z)))
    as (γsb2) "[HownSB2 HownSB2']"; first done.

  iMod (inv_alloc Ns _ (skiplist_prob_inv γst γsb1 γsb2 γb3 S)
          with "[HownST HownSB1 HownSB2 Hemp Hown]") as "Hinvs".
  { iNext. iExists (∅: gset Z), (∅: gset Z). iFrame.
    iSplitL ""; first by auto.
    iRight. rewrite difference_empty elements_empty. done. }

  wp_let.
  wp_alloc bottom_next as "Hb_next".
  iDestruct "Hb_next" as "(Hb_next1&Hb_next2)".
  wp_apply (newlock_spec nroot (∃ np''0 : node_rep, bottom_next ↦{1 / 2} rep_to_node np''0
                                  ∗ own γb3 (GSet (Zlt_range INT_MIN (node_key np''0))))%I
              with "[Hb_next2 HownB3]").
    { iExists right_sentinel. iFrame. }
  iIntros (bottom_lock γ) "His_lock_bottom".

  set (np_new_bottom := (INT_MIN, bottom_next, #(), bottom_lock)).
  rewrite (fold_rep_to_node np_new_bottom).
  wp_let.
  wp_alloc top_next as "Ht_next".
  iDestruct "Ht_next" as "(Ht_next1&Ht_next2)".
  wp_apply (newlock_spec nroot (∃ np''0 : node_rep, top_next ↦{1 / 2} rep_to_node np''0
                                  ∗ own γt3 (GSet (Zlt_range INT_MIN (node_key np''0))))%I
              with "[Ht_next2 HownT3]").
  { iExists right_sentinel. rewrite right_id. iFrame. }
  iIntros (top_lock γ') "His_lock_top".

  set (np_new_top := (INT_MIN, top_next, rep_to_node np_new_bottom, top_lock)).
  rewrite (fold_rep_to_node np_new_top).

  iMod (inv_alloc Nb _ (link_map_inv γb1 γb2 γb3 γb4 np_new_bottom
                               (λ np', ⌜ np' = np_new_bottom ⌝ ∨
                                        own γsb1 (◯ {[ node_key np' ]}))%I)
                  with "[Hb_next1 HownB1 HownB2 HownB4 His_lock_bottom]") as "Hinvb".
  { iNext. iExists ∅, [::], ∅. iFrame.
    iSplitL "".
    { iPureIntro. split; auto. rewrite //=. econstructor; eauto using HMIN_MAX. }
    iSplit.
    * iExists _, _; iFrame.
    * auto.
  }
  iMod (inv_alloc Nt _ (link_map_inv γt1 γt2 γt3 γt4 np_new_top
                           (λ np, ∃ np', ⌜ node_val np = rep_to_node np' ∧
                                           node_key np = node_key np' ⌝ ∗
                                           (⌜ np' = np_new_bottom ⌝ ∨
                                            (own γb1 (◯ {[ np' ]}) ∗ own γsb1 (◯ {[ node_key np' ]})
             )))%I)
    with "[Ht_next1 HownT1 HownT2 HownT4 His_lock_top]") as "Hinvt".
  { iNext. iExists ∅, [::], ∅. iFrame.
    iSplitL "".
    { iPureIntro. split; auto. rewrite //=. econstructor; eauto using HMIN_MAX. }
    iSplit.
    * iExists _, _; iFrame. 
    * iSplit; auto.
  }
  wp_let.
  iApply "HΦ".
  iFrame; auto.
Qed.

Definition cost_top LT k : nat :=
  S (length (list_between LT INT_MIN k)).

Definition ret_top LT k :=
  fold_left Zmax (list_between LT INT_MIN k) INT_MIN. 

Definition cost_bottom LT LB k : nat :=
  S (length (list_between LB (ret_top LT k) k)).
  
Definition level2_cost (LT LB: list Z) k : nat :=
  cost_top LT k + cost_bottom LT LB k.

Definition skip_cost (LT LB: list Z) k : nat :=
  if decide (k ∈ LT) then cost_top LT k else level2_cost LT LB k.

Lemma memSkipList_full_spec Nt Nb γt1 γt2 γt3 γt4 γb1 γb2 γb3 γb4 γsb1
      np_left_top np_left_bottom k ST SB ST_keys SB_keys
      (HkeT: key_equiv ST ST_keys)
      (HkeB: key_equiv SB SB_keys)
      (Hrange: INT_MIN < k ∧ k < INT_MAX)
      (Hnp_left_top: node_key (np_left_top) = INT_MIN)
      (Hnp_left_bot: node_key (np_left_bottom) = INT_MIN):
  {{{
      inv Nt (link_map_inv γt1 γt2 γt3 γt4 np_left_top
                           (λ np, ∃ np', ⌜ node_val np = rep_to_node np' ∧
                                           node_key np = node_key np' ⌝ ∗
                                           (⌜ np' = np_left_bottom ⌝ ∨
                                            (own γb1 (◯ {[ np' ]}) ∗ own γsb1 (◯ {[ node_key np' ]})
             )))) ∗
          inv Nb (link_map_inv γb1 γb2 γb3 γb4 np_left_bottom
                               (λ np', ⌜ np' = np_left_bottom ⌝ ∨
                                        own γsb1 (◯ {[ node_key np' ]}))%I) ∗
      own γt2 (◯! ST) ∗
      own γb2 (◯! SB)
  }}}
    memSkipList (rep_to_node np_left_top) #k
  {{{ (b: bool) (z: Z), RET (#b, #z);
               own γt2 (◯! ST) ∗ own γb2 (◯! SB) ∗
               ⌜ if b then k ∈ ST_keys ∨ k ∈ SB_keys else ¬ (k ∈ ST_keys ∨ k ∈ SB_keys) ⌝ ∗
               ⌜ k ∈ ST_keys → z = cost_top (elements (ST_keys)) k ⌝ ∗
               ⌜ ¬ k ∈ ST_keys → z = level2_cost (elements (ST_keys)) (elements (SB_keys)) k ⌝
  }}}.
Proof.
  destruct Hrange as (Hgt_min&Hlt_max).
  iIntros (Φ) "(#Hinvt&#Hinvb&Hownt&Hownb) HΦ".
  rewrite /addSkipList.
  wp_let. wp_let.
  wp_let. wp_let.
  wp_apply (findPred_aux_spec2 Nt γt1 γt2 γt3 γt4 np_left_top with "[Hownt]").
  { auto. }
  { omega. }
  { iFrame "Hinvt Hownt". iSplit; auto.
    iPureIntro. omega. }
  iIntros (np_pred_top ck_top cmps_top) "(Hownt&Hex&Hpure&Hlock)".
  iDestruct "Hpure" as %(Htop_fold&Hlt_key&Hcmps_top&Hin1&Hin2).
  iDestruct "Hex" as (np_pred_top') "(Hpure&Hnp_pred_top'_handle)".
  iClear "Hlock".
  wp_let.
  wp_proj. wp_let.
  wp_proj. wp_proj. wp_let.
  wp_proj. wp_proj. wp_let.
  wp_op.
  assert (cmps_top = cost_top (elements ST_keys) k).
  { 
    rewrite /cost_top. rewrite Hcmps_top //=.
    subst. rewrite Hnp_left_top.
    rewrite HkeT. auto.
  }

  case_bool_decide; wp_if.
  { iApply "HΦ". iFrame.
    assert (k ∈ ST_keys).
    { 
      rewrite /key_equiv in HkeT. apply elem_of_elements.
      rewrite HkeT. intuition.
    }
    repeat iSplit.
    * iPureIntro; auto.
    * iPureIntro => Hin. auto.
    * iPureIntro; intros; intuition.
  }

  rewrite -fold_rep_to_node.
  wp_let. repeat wp_proj. wp_let. wp_let.
  iDestruct "Hpure" as %(Heqval&Hchild_key).
  rewrite Heqval.
  iApply fupd_wp.
  iInv Nb as "Hinv" "Hclose".

  iDestruct "Hinv" as (SB' LB' SBmap') "(HP&Hlr&>HownSB1'&>HownSB2'&HownSBmap')".
  iAssert (⌜np_pred_top' = np_left_bottom ∨ np_pred_top' ∈ SB⌝)%I
          with "[Hnp_pred_top'_handle Hownb HownSB1' HownSB2']" as "#Hin_bot".
  { 
    iDestruct (own_valid_2 with "HownSB2' Hownb") as % ->%frac_auth_agreeL.
    iDestruct "Hnp_pred_top'_handle" as "[Htop|(Htop&?)]"; auto.
    * iLeft.  auto.
    * iRight.
    - iDestruct (own_valid_2 with "HownSB1' Htop") as
        %[Hvalid%gset_included]%auth_valid_discrete_2.
      iPureIntro. apply Hvalid. apply elem_of_singleton. auto.
  }
  iMod ("Hclose" with "[HP Hlr HownSB1' HownSB2' HownSBmap']").
  { iExists SB', LB', _. iFrame. }
  iModIntro.

  wp_apply (findPred_aux_spec2 Nb γb1 γb2 γb3 γb4 np_left_bottom with "[Hownb]").
  { auto. }
  { omega. }
  { iFrame "Hinvb Hownb". iSplit; auto. iPureIntro; omega. }

  iIntros (np_pred_bottom ck_bottom cmps_bottom) "(Hownb&Hex'&Hpure'&Hlock')".
  iDestruct "Hpure'" as %(Hbot_fold&?&Hcmps_bot&Hin1'&Hin2').
  iClear "Hlock'".

  wp_let. wp_proj.
  wp_let. repeat wp_proj.
  wp_let. repeat wp_proj.
  wp_let.

  assert (¬ k ∈ ST_keys).
  { 
    rewrite /key_equiv in HkeT. intros Hin. apply elem_of_elements in Hin.
    rewrite HkeT in Hin *. intuition.
  }

  wp_op. wp_op. case_bool_decide.
  * iApply "HΦ".
    iFrame. repeat iSplit; iPureIntro.
    ** right.
       rewrite /key_equiv in HkeB. apply elem_of_elements.
       rewrite HkeB. intuition.
    ** intros; intuition.
    ** intros. rewrite /level2_cost.
       rewrite Nat2Z.inj_add; f_equal; auto.
       rewrite /cost_bottom.
       rewrite /ret_top.
       rewrite -Hnp_left_top HkeT.
       rewrite -Htop_fold.
       rewrite Hcmps_bot. rewrite //=.
       rewrite HkeB. rewrite Hchild_key. auto.
  * iApply "HΦ".
    iFrame. repeat iSplit; iPureIntro.
    ** cut (¬ k ∈ SB_keys); first intuition.
       rewrite /key_equiv in HkeB. intros Hin. apply elem_of_elements in Hin.
       rewrite HkeB in Hin *. intuition.
    ** intros; intuition.
    ** intros. rewrite /level2_cost.
       rewrite Nat2Z.inj_add; f_equal; auto.
       rewrite /cost_bottom.
       rewrite /ret_top.
       rewrite -Hnp_left_top HkeT.
       rewrite -Htop_fold.
       rewrite Hcmps_bot. rewrite //=.
       rewrite HkeB. rewrite Hchild_key //=.
Qed.

Section gmap_extra.
  Context `{Countable K} {A: ofeT} `{OfeDiscrete A}.
  Implicit Types m : gmap K (agree A).
  Implicit Types i : K.
  Implicit Types x y : agree A.
  Lemma gmap_existing_local_update m1 m2 i x :
    m1 !! i ≡ Some x → (m1,m2) ~l~> (m1, <[i:=x]>m2).
  Proof using Type*.
    intros Hm1.
    assert (m1 ≡ (<[i := x]>m1)) as Hequiv.
    { intros j. destruct (decide (i = j)) as [->|].
      * rewrite lookup_insert Hm1 //=.
      * rewrite lookup_insert_ne //=.
    }
    destruct (m2 !! i) as [y|] eqn:Heq.
    - rewrite {2}Hequiv.
      apply local_update_valid => Hv1 Hv2 _.
      edestruct (to_agree_uninj x) as (nr&Heq_nr).
        { specialize (Hv1 i). rewrite Hm1 //= in Hv1. }
      assert (∃ e, m1 !! i = Some e ∧ e ≡ (to_agree nr)) as (e&Heq_m1&Hequiv_e).
      {  
        destruct (m1 !! i) as [e|] eqn:Heq_m1; last first.
        { inversion Hm1. }
        exists e; split; eauto.
        cut (Some e ≡ Some (to_agree nr)).
        { intros ?%Some_equiv_inj. auto. }
        rewrite Hm1 Heq_nr.  done.
      }
      eapply insert_local_update; eauto.
      apply local_update_valid.
      * intros Hval1 Hval2 [Hequiv_ey|Hincl].
        ** rewrite -Hequiv_ey -Heq_nr Hequiv_e. reflexivity. 
        ** apply agree_included in Hincl. move: Hval1. rewrite {1}Hincl.
           intros ->%agree_op_inv. rewrite Hequiv_e Heq_nr. reflexivity.
    - apply local_update_unital_discrete=> mf Hmv Hm; simpl in *.
      split; auto using insert_validN.
      assert (Hlookup_mf: mf !! i ≡ Some x).
      { specialize (Hm i). rewrite lookup_op Heq //= in Hm. 
        rewrite /op/cmra_op/option_op//= in Hm.
        destruct (mf !! i) as [y|] eqn:Heq_mf.
        * rewrite Heq_mf Hm1 in Hm *.
          auto.
        * rewrite Heq_mf in Hm. rewrite Hm1 in Hm *. inversion 1.
      }
      intros j; destruct (decide (i = j)) as [->|].
      * rewrite lookup_op lookup_insert Hlookup_mf //=.
        rewrite /op/cmra_op/option_op//= agree_idemp Hm1 //=.
      * rewrite lookup_op lookup_insert_ne //= -lookup_op. apply Hm.
  Qed.
End gmap_extra.

Lemma is_map_of_nset_lookup_inj S Smap nr1 nr2:
  is_map_of_nset S Smap →
  nr1 ∈ S → nr2 ∈ S →
  node_key nr1 = node_key nr2 →
  nr1 = nr2.
Proof.
  intros (Hmap1&Hmap2) Hin1 Hin2 Hkey.
  cut (Some (to_agree nr1) ≡ Some (to_agree nr2)).
  { intros ?%Some_equiv_inj%to_agree_inj. done. }
  rewrite -Hmap1 // -Hmap1 //. rewrite Hkey. done.
Qed.

Lemma is_map_of_nset_subset_insert S1 S1map S2 S2map np_new:
  ✓ S2map →
  is_map_of_nset S1 S1map →
  is_map_of_nset S2 S2map →
  S2 ⊆ S1 →
  np_new ∈ S1 →
  is_map_of_nset (S2 ∪ {[np_new]}) (<[node_key np_new := to_agree np_new]> S2map).
Proof.
  intros Hval (Hm1a&Hm1b) (Hm2a&Hm2b) Hsub Hin.
  destruct (decide (np_new ∈ S2)).
  * split.
    ** intros nr Hin_nr. destruct (decide (node_key nr = node_key np_new)) as [Heq|Hneq].
       *** rewrite Heq lookup_insert.
           rewrite -Hm1a // -Hm1a //; last by set_solver.
           rewrite Heq //=.
       *** rewrite lookup_insert_ne //=. eapply Hm2a.
           apply elem_of_union in Hin_nr as [|?%elem_of_singleton]; auto; congruence.
    ** intros k nr. destruct (decide (k = node_key np_new)) as [Heq|Hneq].
       *** rewrite Heq lookup_insert. 
           intros Heq'%Some_equiv_inj%to_agree_inj. inversion Heq'; subst. split; auto; set_solver+.
       *** rewrite lookup_insert_ne //= => Hequiv.
           edestruct (Hm2b k); eauto.  split; auto. set_solver.
  * apply is_map_of_nset_insert; first (split; eauto).
    destruct (S2map !! node_key np_new) as [e|] eqn:Heq => //=.
    edestruct (to_agree_uninj e) as (nr&Heq').
    { specialize (Hval (node_key np_new)). rewrite Heq //= in Hval. }
    feed pose proof (Hm2b (node_key np_new) nr) as His.
    { rewrite Heq Heq' //=. }
    destruct His as (?&?).
    assert (nr ∈ S1); first by set_solver.
    feed pose proof (Hm1a nr); eauto.
    feed pose proof (is_map_of_nset_lookup_inj S1 S1map nr np_new); eauto.
    { split; auto.  }
    subst. exfalso; eauto.
Qed.

Lemma is_map_nset_union_lookup x S1 S2 S1_map S2_map:
  is_map_of_nset S1 S1_map →
  is_map_of_nset S2 S2_map →
  ✓ (S1_map ⋅ S2_map) →
  x ∈ S1 ∪ S2  →
  (S1_map ⋅ S2_map) !! (node_key x) ≡ Some (to_agree x).
Proof.
  intros Hm1 Hm2 Hval Hin.
  feed pose proof (cmra_valid_op_r _ _ Hval) as Hval1.
  feed pose proof (cmra_valid_op_l _ _ Hval) as Hval2.
  destruct Hm1 as (Hm1a&Hm1b).
  destruct Hm2 as (Hm2a&Hm2b).
  specialize (Hval (node_key x)).
  move: Hval.
  rewrite lookup_op.
  apply elem_of_union in Hin as [Hin|Hin].
  - rewrite Hm1a //=.
    destruct (S2_map !! node_key x) as [|] eqn:Heq; rewrite Heq.
    * rewrite -Some_op. intros ->%agree_op_inv. rewrite agree_idemp //=.
    * rewrite //=.
  - rewrite Hm2a //=.
    destruct (S1_map !! node_key x) as [|] eqn:Heq; rewrite Heq.
    * rewrite -Some_op. intros ->%agree_op_inv. rewrite agree_idemp //=.
    * rewrite //=.
Qed.

Lemma is_map_of_nset_union S1 S2 S1_map S2_map:
  is_map_of_nset S1 S1_map →
  is_map_of_nset S2 S2_map →
  ✓ (S1_map ⋅ S2_map) →
  is_map_of_nset (S1 ∪ S2) (S1_map ⋅ S2_map).
Proof.
  intros Hm1 Hm2 Hvalid.
  split.
  - intros nr Hin. rewrite is_map_nset_union_lookup //=.
  - intros k nr. rewrite lookup_op.
    feed pose proof (cmra_valid_op_r _ _ Hvalid) as Hval2.
    feed pose proof (cmra_valid_op_l _ _ Hvalid) as Hval1.
    specialize (Hvalid k).
    move: Hvalid.
    rewrite lookup_op.
    specialize (Hval1 k). specialize (Hval2 k).
    destruct (S1_map !! k) as [e1|] eqn:Heq1; rewrite ?Heq1;
      destruct (S2_map !! k) as [e2|] eqn:Heq2; rewrite ?Heq2.
    * edestruct (to_agree_uninj e1) as (nr1&Heq1r); eauto.
      { rewrite Heq1 //= in Hval1. }
      edestruct (to_agree_uninj e2) as (nr2&Heq2r); eauto.
      { rewrite Heq2 //= in Hval2. }
      rewrite -Heq1r -Heq2r -Some_op.
      intros ->%agree_op_inv. rewrite agree_idemp.
      intros Heq%Some_equiv_inj%to_agree_inj.
      destruct Hm2 as (?&Hm2'); edestruct Hm2'; eauto.
      { erewrite Heq2; erewrite Heq2r => //=. }
      inversion Heq; subst.
      split; auto. apply elem_of_union_r; eauto.
    * edestruct (to_agree_uninj e1) as (nr1&Heq1r); eauto.
      { rewrite Heq1 //= in Hval1. }
      intros _. rewrite -Heq1r.
      intros Heq%Some_equiv_inj%to_agree_inj.
      destruct Hm1 as (?&Hm2'); edestruct Hm2'; eauto.
      { erewrite Heq1; erewrite Heq1r => //=. }
      inversion Heq; subst.
      split; auto. apply elem_of_union_l; eauto.
    * edestruct (to_agree_uninj e2) as (nr2&Heq2r); eauto.
      { rewrite Heq2 //= in Hval2. }
      intros _. rewrite -Heq2r.
      intros Heq%Some_equiv_inj%to_agree_inj.
      destruct Hm2 as (?&Hm2'); edestruct Hm2'; eauto.
      { erewrite Heq2; erewrite Heq2r => //=. }
      inversion Heq; subst.
      split; auto. apply elem_of_union_r; eauto.
    * inversion 2.
Qed.

Lemma key_equiv_union ST' ST2' ST1 ST2 ST_map' ST_map2'
      (HkeT : key_equiv ST' ST1)
      (HkeT2 : key_equiv ST2' ST2)
      (HmapT : is_map_of_nset ST' ST_map')
      (HmapT2 : is_map_of_nset ST2' ST_map2')
      (Hval : ✓ (ST_map' ⋅ ST_map2')):
  key_equiv (ST' ∪ ST2') (ST1 ∪ ST2).
Proof.
  apply NoDup_Permutation.
  ** apply NoDup_elements. 
  ** apply NoDup_inj_in_map'; last apply NoDup_elements.
     intros x y. rewrite ?elem_of_elements => Hinx Hiny Hnode.
     eapply (is_map_of_nset_lookup_inj (ST' ∪ ST2') (ST_map' ⋅ ST_map2'));
       eauto using is_map_of_nset_union.
  ** intros x; split.
     *** intros Hin%elem_of_elements.
         apply elem_of_union in Hin as [Hin|Hin].
         **** assert (x ∈ (map node_key (elements ST'))) as Hin_map.
              { rewrite -HkeT elem_of_elements //=. }
              apply elem_of_list_In, in_map_iff in Hin_map as (x'&?&?).
              apply elem_of_list_In, in_map_iff.
              eexists; split; eauto. apply elem_of_list_In, elem_of_elements.
              apply elem_of_union_l. apply elem_of_elements, elem_of_list_In; auto.
         **** assert (x ∈ (map node_key (elements ST2'))) as Hin_map.
              { rewrite -HkeT2 elem_of_elements //=. }
              apply elem_of_list_In, in_map_iff in Hin_map as (x'&?&?).
              apply elem_of_list_In, in_map_iff.
              eexists; split; eauto. apply elem_of_list_In, elem_of_elements.
              apply elem_of_union_r. apply elem_of_elements, elem_of_list_In; auto.
     *** intros Hin%elem_of_list_In. apply in_map_iff in Hin as (x'&?&Hin).
         apply elem_of_list_In, elem_of_elements in Hin.
         apply elem_of_union in Hin as [Hin|Hin].
         **** apply elem_of_elements, elem_of_union_l.
              rewrite /key_equiv in HkeT. apply elem_of_elements. rewrite HkeT.
              apply elem_of_list_In, in_map_iff; eexists; split; eauto.
              apply elem_of_list_In, elem_of_elements; auto.
         **** apply elem_of_elements, elem_of_union_r.
              rewrite /key_equiv in HkeT. apply elem_of_elements. rewrite HkeT2.
              apply elem_of_list_In, in_map_iff; eexists; split; eauto.
              apply elem_of_list_In, elem_of_elements; auto.
Qed.

Lemma key_equiv_insert_nin ST ST_keys np:
  key_equiv ST ST_keys →
  ¬ (node_key np ∈ ST_keys) →
  key_equiv (ST ∪ {[ np ]}) (ST_keys ∪ {[ node_key np ]}).
Proof.
  rewrite /key_equiv.
  intros ? Hnin.
  rewrite @union_comm [a in Permutation _ (map _ (elements a))]@union_comm.
  rewrite ?elements_union_singleton //=.
  *** econstructor; eauto.
  *** eapply key_equiv_nin; eauto.
Qed.

Lemma is_map_of_nset_singleton np:
  is_map_of_nset {[np]} {[ node_key np := to_agree np]}.
Proof.
  split.
  - intros ? ?%elem_of_singleton; subst. rewrite lookup_singleton //=.
  - intros k nr.
    destruct (decide (k = node_key np)) as [->|Hneq].
    * rewrite lookup_singleton //=. intros []%Some_equiv_inj%to_agree_inj; split; auto.
      set_solver.
    * rewrite lookup_singleton_ne //=. inversion 1.
Qed.

Lemma key_equiv_singleton np:
  key_equiv {[np]} {[node_key np]}.
Proof. rewrite /key_equiv !elements_singleton //=. Qed.

Lemma add_spec Nt Nb Ns γt1 γt2 γt3 γt4 γb1 γb2 γb3 γb4 γst γsb1 γsb2
      np_left_top np_left_bottom k ST ST_keys ST_map SB SB_keys SB_map Sroot q
      (Hrange: INT_MIN < k ∧ k < INT_MAX)
      (HS: k ∈ Sroot)
      (HmapT: is_map_of_nset ST ST_map)
      (HmapB: is_map_of_nset SB SB_map)
      (HkeT: key_equiv ST ST_keys)
      (HkeB: key_equiv SB SB_keys)
      (Hnp_left_top: node_key (np_left_top) = INT_MIN)
      (Hnp_left_bot: node_key (np_left_bottom) = INT_MIN):
  {{{
      inv Nt (link_map_inv γt1 γt2 γt3 γt4 np_left_top
                           (λ np, ∃ np', ⌜ node_val np = rep_to_node np' ∧
                                           node_key np = node_key np' ⌝ ∗
                                           (⌜ np' = np_left_bottom ⌝ ∨
                                            (own γb1 (◯ {[ np' ]}) ∗ own γsb1 (◯ {[ node_key np' ]})
             )))) ∗
          inv Nb (link_map_inv γb1 γb2 γb3 γb4 np_left_bottom
                               (λ np', ⌜ np' = np_left_bottom ⌝ ∨
                                        own γsb1 (◯ {[ node_key np' ]}))%I) ∗
      inv Ns (skiplist_prob_inv γst γsb1 γsb2 γb3 Sroot) ∗
      own γt2 (◯!{q} ST) ∗
      own γt4 (◯ ST_map) ∗
      own γb2 (◯!{q} SB) ∗
      own γb4 (◯ SB_map) ∗
      own γst (◯!{q} ST_keys) ∗
      own γsb2 (◯!{q} SB_keys) 
  }}}
    addSkipList (rep_to_node np_left_top) #k
    {{{ RET #(); ∃ ST' ST'_keys ST'_map np', ⌜ node_key np' = k ∧ ST ⊆ ST' ∧ key_equiv ST' ST'_keys ∧
                                               key_equiv (SB ∪ {[ np']}) (SB_keys ∪ {[ k ]}) ⌝ ∗
               own γt2 (◯!{q} ST') ∗
               own γb2 (◯!{q} (SB ∪ {[ np' ]})) ∗
               own γst (◯!{q} ST'_keys) ∗
               own γsb2 (◯!{q} (SB_keys ∪ {[ k ]})) ∗
               own γb4 (◯ <[node_key np' := to_agree np']>SB_map) ∗
               own γt4 (◯ ST'_map) ∗
               ⌜ is_map_of_nset ST' ST'_map ∧
                 is_map_of_nset (SB ∪ {[ np' ]}) (<[node_key np' := to_agree np']>SB_map) ⌝
  }}}.
Proof.
  destruct Hrange as (Hgt_min&Hlt_max).
  iIntros (Φ) "(#Hinvt&#Hinvb&Hinvs&Hownt&Hownt_map&Hownb&Hownb_map&Hownst&Hownsb) HΦ".
  rewrite /addSkipList.
  wp_let. wp_let.
  wp_apply (findLockPred_spec); auto.
  { iFrame "Hinvt". rewrite Hnp_left_top; auto. }
  iIntros (np' ck') "(#Hnp'_handle&Hnp'_range&Hnp'_val&Hnp'_succ)".
  iDestruct "Hnp'_val" as (np'_bot) "(Hnp'_bot_eq&#Hnp'_bot_handle)".
  iDestruct "Hnp'_bot_eq" as %(Hnp'_bot_eq&Hnp'_bot_key).
  iDestruct "Hnp'_range" as %Hnp'_range.
  wp_let. wp_proj. wp_let. wp_proj. wp_let.
  destruct_decide (decide (ck' = k)) as Hcase.
  {
    (* Already in top list *)
     wp_bind (BinOp _ _ _).
     iDestruct "Hnp'_succ" as (np'_succ ? ?) "(His_lock&Hlocked&Hpt&Htok&%&Hsucc_case)".
     iDestruct "Hsucc_case" as "[Hright_sent|(?&Hbot_succ)]".
     { iDestruct "Hright_sent" as %Hright_sent. exfalso.
       rewrite /right_sentinel in Hright_sent *.
       subst. rewrite /node_key //= in Hlt_max. omega.
     }
     iDestruct "Hbot_succ" as (np''_succ) "(%&Hbot_succ_handle)".
     iDestruct "Hbot_succ_handle" as "[Hleft|(Hin&Hins)]".
     { iDestruct "Hleft" as %Hleft. exfalso. subst. omega. }
     iInv Nb as "Hinv" "Hclose_bot".
     iDestruct "Hinv" as (S L Smap) "(>H1a&Hlink&HownS1&HownS2&HownSmap)".
     iDestruct "H1a" as %(Hperm&Hsorted&Hnset).
     iMod "HownS1". iMod "HownS2". iMod "HownSmap".
     iDestruct (own_valid_2 with "HownS1 Hin") as
        %[Hvalid%gset_included]%auth_valid_discrete_2.
     iDestruct (own_valid_2 with "HownS2 Hownb") as
         %Hsub%frac_auth_included_total.
     apply gset_included in Hsub.
     iDestruct (own_valid_2 with "HownSmap Hownb_map") as
         %Hsub_map%auth_valid_discrete_2.

     iMod (own_update_2 with "HownS2 Hownb") as "[HownS2 Hownb]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[np''_succ]}); reflexivity. }
     assert (S ∪ {[np''_succ]} ≡ S) as ->.
     { set_solver. }

     iDestruct "Hownb_map" as "#Hownb_map_pers".

     iMod (own_update_2 with "HownSmap Hownb_map_pers") as "[HownSmap Hownb_map]".
     { apply auth_update, (gmap_existing_local_update _ _ (node_key np''_succ) (to_agree np''_succ)).
       destruct Hnset as (HSmap1&HSmap2).  apply HSmap1. set_solver.
     }

     iMod (own_update with "HownSmap") as "[HownSmap Hownb_map_singleton]".
     { apply auth_update_alloc,
         (gmap_existing_local_update _ _ (node_key np''_succ) (to_agree np''_succ)).
       destruct Hnset as (HSmap1&HSmap2).  apply HSmap1. set_solver.
     }

     iDestruct (own_valid_2 with "Hownb_map_pers Hownb_map_singleton") as %Hval_single.
     iClear "Hownb_map_singleton Hownb_map_pers".

     wp_op.
     iMod ("Hclose_bot" with "[Hlink HownS1 HownS2 HownSmap]").
     { iNext.  iExists S, L, _. iFrame. auto. }

     iInv Ns as "Hinv" "Hclose_skip".
     iDestruct "Hinv" as (ST_keys' SB_keys') "(>%&HownST&HownSB1&HownSB2&Hrest)".
     iMod "HownSB1". 
     iDestruct (own_valid_2 with "HownSB1 Hins") as
        %[?%gset_included]%auth_valid_discrete_2.
     iMod "HownSB2". 
     iMod (own_update_2 with "HownSB2 Hownsb") as "[HownSB2 Hownsb]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[node_key np''_succ]}); reflexivity. }
     assert (SB_keys' ∪ {[node_key np''_succ]} ≡ SB_keys') as ->.
     { set_solver. }
     iMod ("Hclose_skip" with "[HownST HownSB1 HownSB2 Hrest]").  
     { iNext. iExists ST_keys', SB_keys'. iFrame; auto. }

     iModIntro.
     case_bool_decide; last by eauto.
     wp_if.
     rewrite -?fold_rep_to_node. wp_let. repeat wp_proj.
     iPoseProof (release_spec with "[His_lock Hlocked Hpt Htok]") as "Hpf".
     { iFrame "His_lock". iFrame. iExists _. iFrame. }
     iApply "Hpf". iNext. iIntros. iApply "HΦ".
     iExists ST, ST_keys, ST_map, np''_succ.
     assert (k = node_key np''_succ) as ->.
     { subst. intuition. }
     iFrame. iPureIntro; split_and!; auto.
     * eapply key_equiv_union; auto.
       { apply key_equiv_singleton. }
       { eauto. }
       { eapply is_map_of_nset_singleton. }
       { rewrite //= in Hval_single. }
     * eapply is_map_of_nset_subset_insert; eauto.
       ** destruct Hsub_map. eapply cmra_valid_included; eauto.
       ** set_solver.
  }
  wp_op. case_bool_decide; first by eauto.
  wp_if.

  rewrite -[a in (nodeVal a)]fold_rep_to_node. wp_let. do 3 wp_proj.
  rewrite Hnp'_bot_eq.
  wp_apply (findLockPred_spec); auto.
  { iFrame "Hinvb". rewrite -Hnp'_bot_key; iSplitR ""; last by (iPureIntro; omega).
    iDestruct "Hnp'_bot_handle" as "[?|(?&?)]";  auto.
  }
  iIntros (np'' ck'') "(#Hnp''_handle&Hnp''_range&_&Hnp''_succ)".
  iDestruct "Hnp''_range" as %Hnp''_range.
  wp_let. repeat wp_proj.
  wp_let. repeat wp_proj.
  wp_let.
  destruct_decide (decide (ck'' = k)) as Hcase''.
  { 
    (* Already in bottom list *)
     wp_bind (BinOp _ _ _).
     iDestruct "Hnp''_succ" as (np''_succ ? ?) "(His_lock&Hlocked&Hpt&Htok&%&Hsucc_case)".
     iDestruct "Hsucc_case" as "[Hright_sent|(Hin&Hins)]".
     { iDestruct "Hright_sent" as %Hright_sent. exfalso.
       rewrite /right_sentinel in Hright_sent *.
       subst. rewrite /node_key //= in Hlt_max. omega.
     }
     iDestruct "Hins" as "[Hins|Hins]".
     { iDestruct "Hins" as %Hleft. exfalso.
       apply (f_equal node_key) in Hleft. rewrite Hnp_left_bot in Hleft. omega. }
     iInv Nb as "Hinv" "Hclose_bot".
     rewrite //=. rewrite /link_map_inv.
     iDestruct "Hinv" as (S L Smap) "(>H1a&Hlink&HownS1&HownS2&HownSmap)".
     iDestruct "H1a" as %(Hperm&Hsorted&Hnset).
     iMod "HownS1". iMod "HownS2". iMod "HownSmap".
     iDestruct (own_valid_2 with "HownS1 Hin") as
        %[Hvalid%gset_included]%auth_valid_discrete_2.
     iDestruct (own_valid_2 with "HownS2 Hownb") as
         %Hsub%frac_auth_included_total.
     apply gset_included in Hsub.

     iMod (own_update_2 with "HownS2 Hownb") as "[HownS2 Hownb]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[np''_succ]}); reflexivity. }
     assert (S ∪ {[np''_succ]} ≡ S) as ->.
     { set_solver. }

     iDestruct "Hownb_map" as "#Hownb_map_pers".

     iDestruct (own_valid_2 with "HownSmap Hownb_map_pers") as
         %Hsub_map%auth_valid_discrete_2.
     iMod (own_update_2 with "HownSmap Hownb_map_pers") as "[HownSmap Hownb_map]".
     { apply auth_update, (gmap_existing_local_update _ _ (node_key np''_succ) (to_agree np''_succ)).
       destruct Hnset as (HSmap1&HSmap2).  apply HSmap1. set_solver.
     }

     iMod (own_update with "HownSmap") as "[HownSmap Hownb_map_singleton]".
     { apply auth_update_alloc,
         (gmap_existing_local_update _ _ (node_key np''_succ) (to_agree np''_succ)).
       destruct Hnset as (HSmap1&HSmap2).  apply HSmap1. set_solver.
     }

     iDestruct (own_valid_2 with "Hownb_map_pers Hownb_map_singleton") as %Hval_single.
     iClear "Hownb_map_singleton Hownb_map_pers".


     wp_op.
     iMod ("Hclose_bot" with "[Hlink HownS1 HownS2 HownSmap]").
     { iNext.  iExists S, L, Smap. iFrame. auto. }

     iInv Ns as "Hinv" "Hclose_skip".
     iDestruct "Hinv" as (ST_keys' SB_keys') "(>%&HownST&HownSB1&HownSB2&Hrest)".
     iMod "HownSB1". 
     iDestruct (own_valid_2 with "HownSB1 Hins") as
        %[?%gset_included]%auth_valid_discrete_2.
     iMod "HownSB2". 
     iMod (own_update_2 with "HownSB2 Hownsb") as "[HownSB2 Hownsb]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[node_key np''_succ]}); reflexivity. }
     assert (SB_keys' ∪ {[node_key np''_succ]} ≡ SB_keys') as ->.
     { set_solver. }
     iMod ("Hclose_skip" with "[HownST HownSB1 HownSB2 Hrest]").  
     { iNext. iExists ST_keys', SB_keys'. iFrame; auto. }


     iModIntro.
     case_bool_decide; last by eauto.
     wp_if. wp_let.
     rewrite -?fold_rep_to_node. wp_let. repeat wp_proj.
     iDestruct "Hnp'_succ" as (? ? ?) "(His_lock'&Hlocked'&Hpt'&Htok'&?)".
     iPoseProof (release_spec with "[His_lock' Hlocked' Hpt' Htok']") as "Hpf".
     { iFrame "His_lock'". iFrame. iExists _. iFrame. }
     wp_apply "Hpf".  iIntros. wp_let.

     wp_let. repeat wp_proj.
     iPoseProof (release_spec with "[His_lock Hlocked Hpt Htok]") as "Hpf".
     { iFrame "His_lock". iFrame. iExists _. iFrame. }
     iApply "Hpf". iNext. iIntros. iApply "HΦ".
     iExists ST, ST_keys, ST_map, np''_succ.
     assert (k = node_key np''_succ) as ->.
     { subst. intuition. }
     iFrame. iPureIntro; split_and!; auto.
     * eapply key_equiv_union; auto.
       { apply key_equiv_singleton. }
       { eauto. }
       { eapply is_map_of_nset_singleton. }
       { rewrite //= in Hval_single. }
     * eapply is_map_of_nset_subset_insert; eauto.
       ** destruct Hsub_map. eapply cmra_valid_included; eauto.
       ** set_solver.
  }
  wp_op. case_bool_decide; first by auto. wp_if.
    rewrite -fold_rep_to_node. wp_let; repeat wp_proj.
    iDestruct "Hnp''_succ" as (np''_succ ? ?) "(His_lock&Hlocked&Hpt&Htok&Hkey&Hsucc_handle)".
    wp_load.
    wp_alloc bottom_next as "Hb_next".
    iDestruct "Hb_next" as "(Hb_next1&Hb_next2)".
    iDestruct "Hkey" as %Hnp''_succ_key.
    rewrite (Zlt_range_split_op (node_key np'') (node_key np''_succ) k); last by omega.
    iDestruct "Htok" as "((Htok_range1&Htok_range2)&Htok_k)".
    wp_apply (newlock_spec nroot (∃ np''0 : node_rep, bottom_next ↦{1 / 2} rep_to_node np''0
                                  ∗ own γb3 (GSet (Zlt_range k (node_key np''0))))%I
              with "[Hb_next2 Htok_range2]").
    { iExists _. iFrame. }
    iIntros (bottom_lock γ) "His_lock_bottom".
    wp_let.

    wp_bind (flip #1 #2).
    iInv Ns as "Hinv" "Hclose".
    iDestruct "Hinv" as (ST_keys' SB_keys')
                          "(>%&HownST_keys'&HownSB1_keys'&HownSB2_keys'&Hown_toks&HProb)".
    iMod "HProb".
    iDestruct "HProb" as "[Hbad|HProb]".
    { iDestruct (own_valid_2 with "Hbad Hownsb") as %?%frac_auth_frag_valid_op_1_l; done. }
    iMod "Hown_toks".
    iDestruct (own_valid_2 with "Hown_toks Htok_k") as 
        %Hdisj%gset_disj_valid_op.

    assert (Permutation (elements (Sroot ∖ SB_keys'))
                        (k :: elements (Sroot ∖ SB_keys' ∖ {[ k ]}))) as Heq_keys.
    {
      rewrite -elements_union_singleton; last by set_solver+.
      apply elements_proper.
      cut (k ∈ (Sroot ∖ SB_keys')).
      { clear. intros. rewrite singleton_union_difference. set_solver. }
      set_solver.
    }
    setoid_rewrite Heq_keys.
    iAssert _ with "[HProb]" as "HProb".
    { iClear "#". setoid_rewrite <-skiplist_unfold_choice. iApply "HProb".
      clear. intros Hin. apply elem_of_elements in Hin. set_solver. }
    
    unshelve (wp_flip _ (λ x y, if (x : bool) then
                                  y = (k :: elements ST_keys')
                                else
                                  y = elements ST_keys') b t Hr).
    { abstract (split; nra). }
    { eapply irrel_coupling_proper.
      { unshelve (setoid_rewrite ivdplus_comm).
        { nra. }
        reflexivity. }
      { reflexivity. }
      apply ip_irrel_coupling.
      eapply ip_coupling_plus; first (by nra);
        apply ip_coupling_mret; auto. }
    iDestruct (own_valid_2 with "HownSB2_keys' Hownsb") as
         %?%frac_auth_included_total%gset_included.
    iDestruct (own_valid_2 with "HownST_keys' Hownst") as
         %?%frac_auth_included_total%gset_included.

     iMod (own_update_2 with "HownSB2_keys' Hownsb") as "[HownSB2_keys' Hownsb]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[k]}); reflexivity. }
     iMod (own_update with "HownSB1_keys'") as "[HownSB1_keys' HownSb1_rem]".
     { apply auth_update_alloc, (gset_local_update_union _ _ {[k]}). }
     rewrite left_id. iDestruct "HownSb1_rem" as "#HownSb1_rem".

    destruct b.
    * iMod (own_update_2 with "HownST_keys' Hownst") as "[HownST_keys' Hownst]".
     { apply frac_auth_update, (gset_local_update_union _ _ {[k]}); reflexivity. }

     iMod ("Hclose" with "[HownST_keys' HownSB1_keys' HownSB2_keys' Hown_toks Htok_k HProb]").
     { iNext. rewrite /skiplist_prob_inv. iExists (ST_keys' ∪ {[ k ]}), (SB_keys' ∪ {[ k ]}).
       iFrame. iSplitL "".
       { iPureIntro. set_solver. }
       iSplitL "Hown_toks Htok_k".
       { rewrite -gset_disj_union //= own_op. iFrame. }
       { rewrite Hr. iClear "#".
         assert (Sroot ∖ (SB_keys' ∪ {[k]}) ≡ Sroot ∖ SB_keys' ∖ {[k]}) as ->.
         { set_solver. }
         rewrite -?elements_union_singleton //=; [ | set_solver | set_solver ].
         assert ((ST_keys' ∪ {[k]}) ≡ {[k]} ∪ ST_keys') as ->.
         { set_solver+. }
         assert ((SB_keys' ∪ {[k]}) ≡ {[k]} ∪ SB_keys') as ->.
         { set_solver+. }
         iRight. done.
       }
     }
     iModIntro.
     wp_op. wp_if. 

     
     set (np_new_bottom := (k, bottom_next, #(), bottom_lock)).
     rewrite (fold_rep_to_node np_new_bottom).
     wp_apply (link_map_insert_spec with
                   "[Hinvb Hb_next1 Hpt Hownb Hownb_map His_lock_bottom HownSb1_rem]"); auto.
     { rewrite {2}/node_key//=.  omega. }
     { rewrite {1}/node_key//=. erewrite Hnp''_succ_key. omega. }
     { eauto. }
     { iFrame "Hinvb Hnp''_handle". iFrame. auto. }
     iIntros "(Hownb2&#Hownbmap'&#Hownb1&%&Hnext)".
     wp_let.
     
     

     rewrite -{-1}[a in (nodeNext a)]fold_rep_to_node.
     wp_let. repeat wp_proj.
     iDestruct "Hnp'_succ" as (np'_succ ? ?)
                                "(His_lock'&Hlocked'&Hpt'&Htok'&Hnp'_succ_key&Hnp'_succ_handle)".
     wp_load.
     wp_alloc top_next as "Ht_next".
     iDestruct "Ht_next" as "(Ht_next1&Ht_next2)".
     iDestruct "Hnp'_succ_key" as %Hnp'_succ_key.
     rewrite (Zlt_range_split_op (node_key np') (node_key np'_succ) k); last omega.
     iDestruct "Htok'" as "((Htok_range1'&Htok_range2')&Htok_k')".
     wp_apply (newlock_spec nroot (∃ np''0 : node_rep, top_next ↦{1 / 2} rep_to_node np''0
                                 ∗ own γt3 (GSet (Zlt_range k (node_key np''0))))%I
                 with "[Ht_next2 Htok_range2']").
     { iExists _; iFrame. }
     iIntros (top_lock γ') "His_lock_top".
     wp_let.
     set (np_new_top := (k, top_next, rep_to_node np_new_bottom, top_lock)).
     rewrite (fold_rep_to_node np_new_top).

     wp_apply (link_map_insert_spec with "[Hinvt Ht_next1 Hpt' Hownt Hownt_map His_lock_top]"); auto.
     { rewrite {2}/node_key//=.  omega. }
     { rewrite {1}/node_key//=. erewrite Hnp'_succ_key. omega. }
     { eapply HmapT. }
     { iFrame "Hinvt Hnp'_handle". iFrame.
       iExists np_new_bottom. iSplitL ""; last first.
       { iRight.  iFrame "HownSb1_rem Hownb1".  }
       iPureIntro. rewrite /np_new_top//=. }
     iIntros "(Hownt2&Howntmap&Hownt1&%&Hpt')".
     wp_let.
     rewrite -?fold_rep_to_node. wp_let. repeat wp_proj.
     iPoseProof (release_spec with "[His_lock' Hlocked' Hpt' Htok_range1']") as "Hpf".
     { iFrame "His_lock'". iFrame. iExists _. iFrame. rewrite /np_new_top//=. }
     wp_apply "Hpf". iIntros. wp_let.


     rewrite -?fold_rep_to_node. wp_let. repeat wp_proj.
     iPoseProof (release_spec with "[His_lock Hlocked Hnext Htok_range1]") as "Hpf".
     { iFrame "His_lock". iFrame. iExists _. iFrame. rewrite /np_new_bottom//=. }
     wp_apply "Hpf". iIntros.
     iApply "HΦ".
     iExists (ST ∪ {[np_new_top]}), (ST_keys ∪ {[ k ]}), _, np_new_bottom; iFrame. iFrame "#".
     iPureIntro; split_and!; auto.
     ** set_solver.
     ** intros. eapply key_equiv_insert_nin; eauto.
        set_solver.
     ** intros. eapply key_equiv_insert_nin; eauto.
        set_solver.
    * iMod ("Hclose" with "[HownST_keys' HownSB1_keys' HownSB2_keys' Hown_toks Htok_k HProb]").
      { iNext. rewrite /skiplist_prob_inv. iExists (ST_keys'), (SB_keys' ∪ {[ k ]}).
        iFrame. iSplitL "".
        { iPureIntro. set_solver. }
        iSplitL "Hown_toks Htok_k".
        { rewrite -gset_disj_union //= own_op. iFrame. }
        { rewrite Hr. iClear "#".
          assert (Sroot ∖ (SB_keys' ∪ {[k]}) ≡ Sroot ∖ SB_keys' ∖ {[k]}) as ->.
          { set_solver. }
          rewrite -?elements_union_singleton //=; [ | set_solver ].
          assert ((SB_keys' ∪ {[k]}) ≡ {[k]} ∪ SB_keys') as ->.
          { set_solver+. }
          iRight. done.
        }
      }
      iModIntro.
      wp_op. wp_if. 

     
     set (np_new_bottom := (k, bottom_next, #(), bottom_lock)).
     rewrite (fold_rep_to_node np_new_bottom).
     wp_apply (link_map_insert_spec with
                   "[Hinvb Hb_next1 Hpt Hownb Hownb_map His_lock_bottom HownSb1_rem]"); auto.
     { rewrite {2}/node_key//=.  omega. }
     { rewrite {1}/node_key//=. erewrite Hnp''_succ_key. omega. }
     { eauto. }
     { iFrame "Hinvb Hnp''_handle". iFrame. auto. }
     iIntros "(Hownb2&#Hownb_map'&#Hownb1&%&Hnext)".
     wp_let.
     
     


      rewrite -fold_rep_to_node. wp_let. repeat wp_proj.
     iDestruct "Hnp'_succ" as (? ? ?) "(His_lock'&Hlocked'&Hpt'&Htok'&?&?)".
     iPoseProof (release_spec with "[His_lock' Hlocked' Hpt' Htok']") as "Hpf".
     { iFrame "His_lock'". iFrame. iExists _. iFrame. }
     wp_apply "Hpf". iIntros. wp_let.


     rewrite -?fold_rep_to_node. wp_let. repeat wp_proj.
     iPoseProof (release_spec with "[His_lock Hlocked Hnext Htok_range1]") as "Hpf".
     { iFrame "His_lock". iFrame. iExists _. iFrame. rewrite /np_new_bottom//=. }
     wp_apply "Hpf". iIntros.
     iApply "HΦ". iExists ST, ST_keys, ST_map, np_new_bottom; iFrame. 
     iFrame "#".
     iPureIntro; split_and!; auto.
     eapply key_equiv_insert_nin; eauto. set_solver.
Time Qed.
Time End proof.
End Skiplist_Raw_Spec.