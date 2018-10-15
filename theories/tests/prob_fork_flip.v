Require Import Reals Psatz.
From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants sts.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation spawn.
From iris.algebra Require Import excl agree csum frac.
From discprob.idxval Require Import pival
     pival_dist ival_dist irrel_equiv idist_pidist_pair extrema.

Program Definition flip_half := pidist_plus (1/2)%R _ (mret true) (mret false).
Next Obligation.
  abstract (nra).
Qed.

Definition one_shotR := csumR (fracR) (agreeR boolC).
Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.

Section proof.
Context `{!heapG Σ, !spawnG Σ, !probG Σ, !one_shotG Σ}.

Definition Pending q : one_shotR := (Cinl q : one_shotR).
Definition Shot (b: bool) : one_shotR := (Cinr (to_agree b) : one_shotR).

Global Instance shot_persistent γ b : Persistent (own γ (Shot b)).
Proof. apply _. Qed.

(* TODO: there's no need to have the starting thread wrap up their ownership into
   this one shot inv; and the flip_inv should not hold "one_shot_inv" but rather 
   just the status of the shot. *)
Definition one_shot_inv (γ : gname) (l : loc) : iProp Σ :=
  (l ↦ NONEV ∨ ∃ b : bool, (l ↦  NONEV ∨ l ↦ SOMEV #b ∗ own γ (Shot b)))%I.

Definition mapsto_shot l (ob : option bool) : iProp Σ :=
  match ob with
    | None => (∃ N γ, inv N (one_shot_inv γ l))%I
    | Some b => (∃ N γ, inv N (one_shot_inv γ l) ∗ own γ (Shot b))%I
  end.

Definition flip_inv (γ : gname) (γ1 γ2: gname) : iProp Σ :=
  ((ownProb flip_half ∗ own γ1 (Pending (1/2)%Qp) ∗ own γ2 (Pending (1/2)%Qp)) ∨
   (∃ b, ownProb flip_half ∗ own γ1 (Shot b) ∗ own γ2 (Pending (1/2)%Qp)) ∨
   (∃ b, ownProb flip_half ∗ own γ1 (Pending (1/2)%Qp) ∗ own γ2 (Shot b)) ∨
   (∃ b1 b2, (own γ (Excl ()) ∨ ownProb (mret (eqb b1 b2)))
                     ∗ own γ1 (Shot b1) ∗ own γ2 (Shot b2)))%I.


Lemma mapsto_shot_load N γ l:
  {{{ inv N (one_shot_inv γ l) }}} Load (Lit (LitLoc l))
  {{{ v, RET v;
      match v with
      | NONEV => True
      | SOMEV #b => ∃ b', ⌜ (LitBool b') = b ⌝ ∗ own γ (Shot b')
      | _  => False
      end}}}.  
Proof.
  iIntros (Φ) "#Hinv Hwand". 
  iInv N as ">[Hnone|Hsome]" "Hclose".
  - wp_load. iApply "Hwand". iMod ("Hclose" with "[Hnone]").
    { iNext. iRight. iExists true. iLeft. iFrame. }
    done.
  - iDestruct "Hsome" as (b') "[Hnone|(Hsome&#Hshot')]".
    * wp_load. iApply "Hwand". iMod ("Hclose" with "[Hnone]").
      { iNext. iRight. iExists true. iLeft. iFrame. }
      iModIntro. done.
    * wp_load. iApply "Hwand".
      iMod ("Hclose" with "[Hsome]").
      { iNext. iRight. iExists b'. iRight. iFrame. done. }
      iModIntro; iExists b'; iSplitR; done.
Qed.


Lemma mapsto_shot_load_some N γ l b:
  {{{ inv N (one_shot_inv γ l) ∗ own γ (Shot b) }}} Load (Lit (LitLoc l))
  {{{ v, RET v;
      match v with
      | NONEV => own γ (Shot b)
      | SOMEV #b' => ⌜ (LitBool b) = b' ⌝ ∗ own γ (Shot b)
      | _  => False
      end}}}.  
Proof.
  iIntros (Φ) "(#Hinv&Hshot) Hwand". 
  iInv N as ">[Hnone|Hsome]" "Hclose".
  - wp_load. iApply "Hwand". iMod ("Hclose" with "[Hnone]").
    { iNext. iRight. iExists true. iLeft. iFrame. }
    done.
  - iDestruct "Hsome" as (b') "[Hnone|(Hsome&Hshot')]".
    * wp_load. iApply "Hwand". iMod ("Hclose" with "[Hnone]").
      { iNext. iRight. iExists true. iLeft. iFrame. }
      iModIntro. done.
    * wp_load. iApply "Hwand".
      iDestruct (own_valid_2 with "Hshot Hshot'") as %?%agree_op_invL'; subst.
      iMod ("Hclose" with "[Hshot' Hsome]").
      { iNext. iRight. iExists b'. iRight. iFrame. }
      iModIntro; iSplitR; done.
Qed.

Lemma mapsto_shot_store_some N γ l b:
  {{{ inv N (one_shot_inv γ l) ∗ own γ (Shot b) }}}
    Store (Lit (LitLoc l)) (SOMEV (LitV $ LitBool b))
  {{{ RET #(); own γ (Shot b) }}}.
Proof.
  iIntros (Φ) "(#Hinv&Hshot) Hwand". 
  iInv N as ">[Hnone|Hsome]" "Hclose".
  - wp_store. iApply "Hwand".
      iAssert (own γ (Shot b) ∗ own γ (Shot b))%I with "[Hshot]" as "(Hshot1&Hshot2)".
      { rewrite -own_op Cinr_op //=
        -(proj1 (agree_included (to_agree b) (to_agree b))); last reflexivity.
        iFrame. }
      iMod ("Hclose" with "[Hshot1 Hnone]").
      { iNext. iRight. iExists b. iRight. iFrame. }
      iModIntro. done.
  - iDestruct "Hsome" as (b') "[Hnone|(Hsome&Hshot')]".
    * wp_store. iApply "Hwand".
      iAssert (own γ (Shot b) ∗ own γ (Shot b))%I with "[Hshot]" as "(Hshot1&Hshot2)".
      { rewrite -own_op Cinr_op //=
        -(proj1 (agree_included (to_agree b) (to_agree b))); last reflexivity.
        iFrame. }
      iMod ("Hclose" with "[Hshot1 Hnone]").
      { iNext. iRight. iExists b. iRight. iFrame. }
      iModIntro. done.
    * wp_store. iApply "Hwand".
      iDestruct (own_valid_2 with "Hshot Hshot'") as %?%agree_op_invL'; subst.
      iMod ("Hclose" with "[Hshot' Hsome]").
      { iNext. iRight. iExists b'. iRight. iFrame. }
      iModIntro. done.
Qed.

Lemma flip_inv_commit N γ γ1 γ2 γ':
  γ' = γ1 ∨ γ' = γ2 →
  {{{ inv N (flip_inv γ γ1 γ2) ∗ own γ' (Pending (1/2)%Qp) }}}
    flip #1 #2
  {{{ b, RET (LitV $ LitBool b); own γ' (Shot b) }}}.
Proof.
  intros Heq.
  iIntros (Φ) "(#Hinv&Hγ') Hwand". 
  iInv N as ">[Hprob|[Hprob|[Hprob|Hprob]]]" "Hclose".
  * iDestruct "Hprob" as "(Hprob&Hγ1&Hγ2)".
    setoid_rewrite <-(pidist_left_id tt (λ x, flip_half)) at 1.
    unshelve (wp_flip (mret tt) (λ x y, True) b t HR); first by abstract (nra).
    { apply irrel_coupling_trivial. }
    destruct Heq as [Heq|Heq]; subst.
    ** iMod (own_update γ1 (Pending 1%Qp) with "[Hγ' Hγ1]") as "#Hγ'".
       { by apply cmra_update_exclusive with (y:=Shot b). }
       { iCombine "Hγ'" "Hγ1" as "H".
         rewrite //=. rewrite Cinl_op frac_op'. rewrite /Pending.
         by rewrite Qp_div_2. }
       iMod ("Hclose" with "[Hprob Hγ2]").
       { iNext. iRight. iLeft. iExists b. iFrame. done. }
       iModIntro.
       iApply "Hwand"; done.
    ** iMod (own_update γ2 (Pending 1%Qp) with "[Hγ' Hγ2]") as "#Hγ'".
       { by apply cmra_update_exclusive with (y:=Shot b). }
       { iCombine "Hγ'" "Hγ2" as "H".
         rewrite //=. rewrite Cinl_op frac_op'. rewrite /Pending.
         by rewrite Qp_div_2. }
       iMod ("Hclose" with "[Hprob Hγ1]").
       { iNext. iRight. iRight. iLeft. iExists b. iFrame. done. }
       iModIntro.
       iApply "Hwand"; done.
  * destruct Heq as [Heq1|Heq2]; subst.
    { iDestruct "Hprob" as (b) "(Hprob&Hshot&?)".
      iDestruct (own_valid_2 with "Hγ' Hshot") as "%".
      exfalso; auto. }
    
    iDestruct "Hprob" as (b) "(Hprob&Hshot1&Hshot2)".
    setoid_rewrite <-pidist_right_id.
    unshelve (wp_flip flip_half (λ x y, match b, x with
                                               | true, true => y = true
                                               | false, false => y = true
                                               | _, _ => y = false
                                               end) c c' HRc); first by abstract (nra).
    { apply ip_irrel_coupling.
      destruct b.
      * eapply ip_coupling_plus; first (by reflexivity);
          apply ip_coupling_mret; auto.
      * assert (0 <= 1 - (IZR 1 /IZR 2) <= 1)%R by nra.
        eapply (ip_coupling_proper (ivdplus _ H (mret false) (mret true))).
        { symmetry. eapply ivdplus_comm. } 
        { reflexivity.  }
        assert (1 - (IZR 1 / IZR 2) = IZR 1 / IZR 2)%R as Hzeq.
        { nra.  }
        generalize H.
        rewrite Hzeq => ?.
        eapply ip_coupling_plus; first (by reflexivity);
          apply ip_coupling_mret; auto.
    }
    iMod (own_update _ (Pending 1%Qp) with "[Hγ' Hshot2]") as "#Hγ'".
    { by apply cmra_update_exclusive with (y:=Shot c). }
    { iCombine "Hγ'" "Hshot2" as "H".
         rewrite //=. rewrite Cinl_op frac_op'. rewrite /Pending.
         by rewrite Qp_div_2. }
    iMod ("Hclose" with "[Hprob Hshot1]").
    { iNext. iRight. iRight. iRight.
      iExists b, c. iFrame. iFrame "Hγ'".
      iRight. iFrame.
      destruct b, c, c' => //=.
    }
    iModIntro.
    iApply "Hwand". done.
  * destruct Heq as [Heq1|Heq2]; subst; last first.
    { iDestruct "Hprob" as (b) "(Hprob&_&Hshot)".
      iDestruct (own_valid_2 with "Hγ' Hshot") as "%".
      exfalso; auto. }
    iDestruct "Hprob" as (b) "(Hprob&Hshot1&Hshot2)".
    setoid_rewrite <-pidist_right_id.
    unshelve (wp_flip flip_half (λ x y, match b, x with
                                               | true, true => y = true
                                               | false, false => y = true
                                               | _, _ => y = false
                                               end) c c' HRc); first by abstract (nra).
    { apply ip_irrel_coupling.
      destruct b.
      * eapply ip_coupling_plus; first (by reflexivity);
          apply ip_coupling_mret; auto.
      * assert (0 <= 1 - (IZR 1 /IZR 2) <= 1)%R by nra.
        eapply (ip_coupling_proper (ivdplus _ H (mret false) (mret true))).
        { symmetry. eapply ivdplus_comm. } 
        { reflexivity.  }
        assert (1 - (IZR 1 / IZR 2) = IZR 1 / IZR 2)%R as Hzeq.
        { nra.  }
        generalize H.
        rewrite Hzeq => ?.
        eapply ip_coupling_plus; first (by reflexivity);
          apply ip_coupling_mret; auto.
    }
    iMod (own_update _ (Pending 1%Qp) with "[Hγ' Hshot1]") as "#Hγ'".
    { by apply cmra_update_exclusive with (y:=Shot c). }
    { iCombine "Hγ'" "Hshot1" as "H".
         rewrite //=. rewrite Cinl_op frac_op'. rewrite /Pending.
         by rewrite Qp_div_2. }
    iMod ("Hclose" with "[Hprob Hshot2]").
    { iNext. iRight. iRight. iRight.
      iExists c, b. iFrame. iFrame "Hγ'".
      iRight. iFrame.
      destruct b, c, c' => //=.
    }
    iModIntro.
    iApply "Hwand". done.
  * iDestruct "Hprob" as (b1 b2) "(Hprob&Hshot1&Hshot2)".
    destruct Heq as [Heq1|Heq2]; subst.
    ** iDestruct (own_valid_2 with "Hγ' Hshot1") as "%".
       exfalso; auto.
    ** iDestruct (own_valid_2 with "Hγ' Hshot2") as "%".
       exfalso; auto.
Qed.
                 
Lemma join_spec N γ l :
  {{{ inv N (one_shot_inv γ l) }}} join #l {{{ b, RET (LitV $ LitBool b); own γ (Shot b) }}}.
Proof.
  iIntros (Φ) "#Hinv Hwand". 
  iLöb as "IH". wp_rec. wp_bind (! _)%E.
  wp_apply mapsto_shot_load; eauto.
  iIntros (v) "Hret". destruct v; eauto.
  * wp_match. wp_apply "IH"; auto.
  * wp_match. destruct v; eauto.
    iDestruct "Hret" as (b) "(%&Hshot)"; subst.
    iApply "Hwand". done.
Qed.

Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.

Definition concurrent_flip : expr :=
  let: "l" := ref NONE in
  Fork ("l" <- SOME (flip #1 #2)) ;; 
  let: "b" := flip #1 #2 in
  let: "ret" := App join "l" in
  "b" = "ret".

Lemma cflip_spec  :
  ownProb flip_half ⊢
          WP concurrent_flip {{ v, ∃ v', ownProb (mret v') ∗
                                                 ⌜ v = LitV $ LitBool v' ⌝ }}%I.
Proof.
  iIntros "Hprob". rewrite /concurrent_flip.
  wp_alloc l2 as "Hl2". wp_let.
  iMod (own_alloc (Pending 1%Qp)) as (γ1) "Hγ1"; first done.
  rewrite -[a in Pending a](Qp_div_2 1). rewrite /Pending -frac_op' -Cinl_op.
  iDestruct "Hγ1" as "(Hγ1a&Hγ1b)".

  iMod (own_alloc (Pending 1%Qp)) as (γ2) "Hγ2"; first done.
  rewrite -[a in Pending a](Qp_div_2 1). rewrite /Pending -frac_op' -Cinl_op.
  iDestruct "Hγ2" as "(Hγ2a&Hγ2b)".


  pose proof (nroot .@ "N1") as N1.
  pose proof (nroot .@ "N2") as N2.
  iMod (inv_alloc N1 _ (one_shot_inv γ2 l2) with "[Hl2]") as "#HN1".
  { iNext. rewrite /one_shot_inv. iLeft. iFrame. }
  
  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc N2 _ (flip_inv γ γ1 γ2) with "[Hprob Hγ1b Hγ2b]") as "#HN2".
  { iNext. rewrite /flip_inv. iLeft. iFrame. } 

  wp_apply wp_fork.
  iSplitR "Hγ2a"; last first.
  - wp_bind (flip #1 #2). 
    wp_apply (flip_inv_commit N2 γ γ1 γ2 γ2 with "[Hγ2a]"); auto.
    iIntros (b) "#Hγ2".
    wp_apply (mapsto_shot_store_some with "[Hγ2]"); eauto.
  - wp_let. wp_bind (flip #1 #2).
    wp_apply (flip_inv_commit N2 γ γ1 γ2 γ1 with "[Hγ1a]"); auto.
    iIntros (b) "#Hγ1".
    wp_let. wp_apply join_spec; eauto.
    iIntros (b') "#Hγ2".
    wp_let.
    iInv N2 as ">[(_&Hγ1'&_)|[Hprob|[Hprob|Hprob]]]" "Hclose".
    { iDestruct (own_valid_2 with "Hγ1 Hγ1'") as "%".
      exfalso; auto. }
    { iDestruct "Hprob" as (?) "(_&_&Hγ2')".
      iDestruct (own_valid_2 with "Hγ2 Hγ2'") as "%".
      exfalso; auto. }
    { iDestruct "Hprob" as (?) "(_&Hγ1'&_)".
      iDestruct (own_valid_2 with "Hγ1 Hγ1'") as "%".
      exfalso; auto. }
    iDestruct "Hprob" as (b1 b2) "(Hprob&Hγ1'&Hγ2')".
    iDestruct (own_valid_2 with "Hγ1 Hγ1'") as %?%agree_op_invL'; subst.
    iDestruct (own_valid_2 with "Hγ2 Hγ2'") as %?%agree_op_invL'; subst.
    iDestruct "Hprob" as "[Htok|Hprob]".
    { iDestruct (own_valid_2 with "Hγ Htok") as "%".
      exfalso; auto. }
    wp_op.
    iMod ("Hclose" with "[Hγ]").
    { iNext.  iRight. iRight. iRight. iExists b1, b2. iFrame "Hγ1 Hγ2".
      iLeft. done. }
    iModIntro. iExists (eqb b1 b2). iFrame.
    iPureIntro. destruct b1, b2 => //=.
Qed.
End proof.