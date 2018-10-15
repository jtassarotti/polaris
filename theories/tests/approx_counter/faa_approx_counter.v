Require Import Reals Psatz Omega.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iris.heap_lang Require Import proofmode notation par.
From mathcomp Require Import seq fintype.

Section COUNTER.
Variable MAX : nat.

Definition newcounter : val := λ: <>, ref #0.
Definition min : val :=
  λ: "x" "y", if: "x" < "y" then "x" else "y".
Definition incr : val := λ: "l",
    let: "n" := min !"l" #MAX in
    let: "b" := flip #1 ("n" + #1)  in
    if: "b" then
      FAA "l" ("n" + #1);; #()
    else
      #().

Definition read : val := λ: "l", !"l".

From discprob.idxval Require Import pival
     pival_dist ival_dist irrel_equiv idist_pidist_pair extrema pidist_post_cond.

Local Open Scope R_scope.

Lemma INRp1_prob n:
  0 <= 1 / (INR n + 1) <= 1.
Proof.
  split.
  - specialize (RinvN_pos n). intros; nra.
  - replace 1 with (1 / 1) at 3; auto; last nra.
    apply Reals_ext.Rdiv_le_compat_contra; try nra.
    specialize (pos_INR n). nra.
Qed.

From discprob.basic Require Import monad.
Opaque mret.
Opaque mbind.

(* On paper we just write this as (mret 0) U ... U (mret n). *)
Definition select_upto (n: nat) : pidist nat :=
  fold_left pidist_union (map mret (iota 1 n)) (mret O).

Definition flip_incr (n: nat) : pidist nat :=
  pidist_plus (1/(INR n + 1)) (INRp1_prob n) (mret (S n)) (mret O).
  
Definition approx_incr : pidist nat :=
  k ← select_upto MAX;
  flip_incr k.

Fixpoint approx_n (n: nat) (l: nat) : pidist nat :=
  match n with
  | O => mret l
  | S n' =>
    x ← approx_incr;
    approx_n n' (l + x)
  end.

Lemma select_upto_spec1 curr:
  pspec (select_upto curr) (λ x, x  <= curr)%nat.
Proof.
  rewrite /approx_incr/select_upto.
  eapply (pspec_conseq _ (λ x, x <= curr + 0)%nat); last by (intros; omega).
  generalize O.
  induction curr => //= n.
  * apply pspec_mret. omega.
  * rewrite -pidist_union_foldleft_hd.
    apply pspec_union.
    ** apply pspec_mret; auto. omega.
    ** eapply pspec_conseq; first eapply IHcurr.
       rewrite //=. intros a Hle. omega.
Qed.

Lemma approx_incr_bounded:
  pspec (approx_incr) (λ x : nat, Rabs (INR x) <= INR (S MAX)).
Proof.
  eapply (pspec_mbind _ _ (λ x, x <= MAX)%nat); first eapply select_upto_spec1.
  intros a Hle. rewrite /flip_incr.
  apply pspec_pidist_plus.
  * apply pspec_mret. rewrite Rabs_right.
    ** apply le_INR. omega.
    ** apply Rle_ge, pos_INR.
  * apply pspec_mret. rewrite S_INR //= Rabs_R0.
    specialize (pos_INR MAX); nra.
Qed.

Fixpoint approx_n_bound n curr :=
  match n with
  | O => curr
  | S n' =>
    approx_n_bound n' (curr + S MAX)%nat
  end.

Lemma approx_n_bounded_mono n curr curr':
  (curr <= curr')%nat →
  (approx_n_bound n curr <= approx_n_bound n curr')%nat.
Proof.
  revert curr curr'.
  induction n => //=.
  intros curr curr' Hle.
  eapply IHn. omega.
Qed.

Lemma approx_n_bounded n curr:
  pspec (approx_n n curr) (λ x : nat, Rabs (INR x) <= INR (approx_n_bound n curr)).
Proof.
  revert curr.
  induction n => curr.
  - apply pspec_mret => //=. rewrite Rabs_right; last apply Rle_ge, pos_INR.
    reflexivity.
  - rewrite /=.
    eapply pspec_mbind; first eapply approx_incr_bounded.
    intros a. rewrite S_INR => Hle.
    eapply pspec_conseq; first eapply IHn => //=.
    intros k => //=.
    intros. etransitivity; first eassumption. apply le_INR.
    apply approx_n_bounded_mono.
    rewrite Rabs_right in Hle; last apply Rle_ge, pos_INR.
    rewrite -S_INR in Hle. apply INR_le in Hle. omega.
Qed.

Import Rbar.

Lemma Ex_min_approx_incr:
  Ex_min INR (approx_incr) = Finite 1.
Proof.
  rewrite /approx_incr.
  apply Ex_min_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S MAX)).
    apply approx_incr_bounded.
  }
  intros k. rewrite /flip_incr.
  rewrite ?Ex_min_pidist_plus ?Ex_min_mret // ?(S_INR) //=.
  * rewrite //= Rmult_0_r Rplus_0_r. 
    specialize (INRp1_prob k); intros (?&?).
    specialize (Rcomplements.INRp1_pos k). intros.
    f_equal. field. nra.
  * apply ex_Ex_extrema_pidist_plus; apply ex_Ex_extrema_mret.
Qed.

   
Lemma Ex_min_approx_n (n: nat) l:
  Ex_min INR (approx_n n l) =
  Finite (INR (n + l)).
Proof.
  revert l.
  induction n => l.
  - rewrite //=. rewrite Ex_min_mret. done.
  - transitivity (Ex_min (λ x : nat, INR (n + l) + INR x) (approx_incr)).
    { rewrite Ex_min_bind_post -/approx_n.
      * apply Ex_min_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
        nra.
      * apply Ex_min_bounded_supp_fun_finite.
        apply pspec_bounded. 
        eexists (INR (n + l + MAX + 1)). eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn. rewrite ?Rabs_right in Hle *; try apply Rle_ge, pos_INR.
        apply le_INR. apply INR_le in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (approx_n_bound (S n) l)).
        eapply (approx_n_bounded (S n) l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (n + l + (MAX  + 1))).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros k Hb. rewrite IHn.
        rewrite Rabs_right; last by apply Rle_ge, pos_INR.
        apply le_INR.
        rewrite Rabs_right in Hb; last by apply Rle_ge, pos_INR.
        apply INR_le in Hb. omega.
    }
    rewrite Ex_min_plus_const_l.
    rewrite ?plus_INR. rewrite S_INR.
    rewrite Ex_min_approx_incr.
    rewrite //=. f_equal.
    nra.
Qed.

Lemma Ex_max_approx_incr :
  Ex_max INR (approx_incr) = Finite 1.
Proof.
  rewrite /approx_incr.
  apply Ex_max_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S MAX)).
    apply approx_incr_bounded.
  }
  intros k. rewrite /flip_incr.
  rewrite ?Ex_max_pidist_plus ?Ex_max_mret // ?(S_INR) //=.
  * rewrite //= Rmult_0_r Rplus_0_r. 
    specialize (INRp1_prob k); intros (?&?).
    specialize (Rcomplements.INRp1_pos k). intros.
    f_equal. field. nra.
  * apply ex_Ex_extrema_pidist_plus; apply ex_Ex_extrema_mret.
Qed.

Lemma Ex_max_approx_n (n: nat) l:
  Ex_max INR (approx_n n l) =
  Finite (INR (n + l)).
Proof.
  revert l.
  induction n => l.
  - rewrite //=. rewrite Ex_max_mret. done.
  - transitivity (Ex_max (λ x : nat, INR (n + l) + INR x) (approx_incr)).
    { rewrite Ex_max_bind_post -/approx_n.
      * apply Ex_max_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
        nra.
      * apply Ex_max_bounded_supp_fun_finite.
        apply pspec_bounded. 
        eexists (INR (n + l + MAX + 1)). eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn. rewrite ?Rabs_right in Hle *; try apply Rle_ge, pos_INR.
        apply le_INR. apply INR_le in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (approx_n_bound (S n) l)).
        eapply (approx_n_bounded (S n) l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (n + l + (MAX  + 1))).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros k Hb. rewrite IHn.
        rewrite Rabs_right; last by apply Rle_ge, pos_INR.
        apply le_INR.
        rewrite Rabs_right in Hb; last by apply Rle_ge, pos_INR.
        apply INR_le in Hb. omega.
    }
    rewrite Ex_max_plus_const_l.
    rewrite ?plus_INR. rewrite S_INR.
    rewrite Ex_max_approx_incr.
    rewrite //=. f_equal.
    nra.
Qed.

Class acounterG Σ :=
  ACounterG { acounter_inG :> inG Σ (frac_authR natR) }.
Definition acounterΣ : gFunctors := #[GFunctor (frac_authR natR)].
Instance subG_acounterΣ {Σ} : subG acounterΣ Σ → acounterG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{!heapG Σ, !probG Σ, !acounterG Σ, !spawnG Σ}.


Lemma min_spec E (z1 z2: Z):
  {{{ True }}}
    min #z1 #z2 @ E
  {{{ RET LitV (LitInt (Zmin z1 z2)) ; True }}}. 
Proof.
  iIntros (Φ) "_ HΦ".
  iIntros. wp_let. wp_let.
  wp_op; case_bool_decide.
  * wp_if. 
    rewrite Z.min_l; last by omega.
    by iApply "HΦ".
  * wp_if. 
    rewrite Z.min_r; last by omega.
    by iApply "HΦ".
Qed.

(* See the "counter with contribution" example in the "counter.v" file of the heap_lang lib *)
   
(* We first prove an "unbundled" form of the spec, where the invariants are
     separated from the acounter permission. Then, we use these triples to prove
     a bundled spec matching the one given in the paper *)

Definition acounter_loc_inv (γl : gname) (l : loc) : iProp Σ :=
    (∃ n, own γl (●! n) ∗ l ↦ #n)%I.

Definition acounter_prob_inv (γp γv : gname): iProp Σ :=
    (∃ n1 n2, own γp (●! n1) ∗ own γv (●! n2) ∗ (own γp (◯! n1) ∨ ownProb (approx_n n1 n2)))%I.

Definition acounter (γl γp γv : gname) (q : frac) (nperm : nat) (ncontrib : nat) : iProp Σ :=
    (own γp (◯!{q} nperm) ∗ own γl (◯!{q} ncontrib) ∗ own γv (◯!{q} ncontrib))%I.

Lemma acounter_sep γl γp γv q1 q2 np1 np2 nc1 nc2 :
  acounter γl γp γv (q1 + q2) (np1 + np2) (nc1 + nc2) ⊢
           acounter γl γp γv q1 np1 nc1 ∗ acounter γl γp γv q2 np2 nc2.
Proof.
  rewrite /acounter.
  iStartProof. 
  * iIntros "(Hown1&Hown2&Hown3)".  
    rewrite ?frag_auth_op -?own_op.
    iDestruct "Hown1" as "(?&?)". 
    iDestruct "Hown2" as "(?&?)". 
    iDestruct "Hown3" as "(?&?)". 
    iFrame.
Qed.

Lemma acounter_join γl γp γv q1 q2 np1 np2 nc1 nc2 :
  acounter γl γp γv q1 np1 nc1 ∗ acounter γl γp γv q2 np2 nc2 ⊢
           acounter γl γp γv (q1 + q2) (np1 + np2) (nc1 + nc2).
Proof.
  rewrite /acounter.
  iStartProof. 
  * iIntros "((Hown1a&Hown2a&Hown3a)&(Hown1b&Hown2b&Hown3b))".  
    iCombine "Hown1a" "Hown1b" as "Hown1".
    iCombine "Hown2a" "Hown2b" as "Hown2".
    iCombine "Hown3a" "Hown3b" as "Hown3".
    iFrame.
Qed.

Lemma incr_spec N1 N2 γl γp γv l q np nc:
  {{{ inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv γp γv) ∗
      acounter γl γp γv q (S np) nc }}}
    incr (Lit $ LitLoc l) 
  {{{ RET LitV LitUnit; ∃ nc' : nat, acounter γl γp γv q np nc' }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(#Hinv1&#Hinv2&(Hγp&Hγl&Hγv))".
  rewrite /incr.
  wp_let. wp_bind (! _)%E.
  iInv N1 as (c) ">[Hγl' Hl]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hγl' Hl]") as "_".
  { iNext; iExists c; by iFrame. } 

  iModIntro.
  wp_apply min_spec; first done; iIntros "_".
  wp_let. 

  wp_op.
  wp_bind (flip _ _).
  iInv N2 as (np_global nv_global) ">(Hγp'&Hγv'&Hprob)" "Hclose".
  iDestruct "Hprob" as "[Hbad|Hprob]".
  { iDestruct (own_valid_2 with "Hbad Hγp") as %?%frac_auth_frag_valid_op_1_l; done. }

  iDestruct (own_valid_2 with "Hγp' Hγp") as % ?%frac_auth_included_total%nat_included.
  destruct np_global as [|np_global]; first by omega.
  rewrite //=.

  assert (0 <= IZR 1 / IZR (Z.min c MAX + 1) ∧ IZR 1 / IZR (Z.min c MAX + 1) <= 1).
  {
    rewrite //=.
    assert (IZR (Z.min c MAX + 1) = INR (Z.to_nat (Z.min c MAX) + 1)).
    rewrite INR_IZR_INZ; f_equal.
    assert (0 ≤ Z.min c MAX).
    { apply Z.min_glb; omega. }
    replace 1%nat with (Z.to_nat 1); try auto.
    rewrite -Z2Nat.inj_add; try omega.
    { rewrite Z2Nat.id => //=. etransitivity; first eauto.
      rewrite //=.  omega.
    }
    rewrite H. destruct (INRp1_prob (Z.to_nat (Z.min c MAX))).
    split; auto; etransitivity; eauto; rewrite plus_INR //=.
  }

  unshelve (wp_flip (approx_incr)
                    (λ x y, if (x : bool) then (Z.of_nat y) = (Z.min c MAX + 1)%Z
                            else Z.of_nat y = O) b z' HR); auto.
    { rewrite /approx_incr/select_upto. eapply irrel_coupling_proper.
      { reflexivity.  }
      { setoid_rewrite pidist_union_foldleft_bind. reflexivity. }
      apply ip_irrel_coupling.
      eapply (ip_coupling_union_list _ (flip_incr (Z.to_nat (Z.min c MAX)))).
      - rewrite /flip_incr.
        apply ip_coupling_plus.
        { rewrite //=.  f_equal. rewrite plus_IZR. f_equal.
          rewrite INR_IZR_INZ. f_equal.
          rewrite Z2Nat.id; auto.
          apply Z.min_glb; omega.
        }
        * apply ip_coupling_mret.
          rewrite -Z2Nat.inj_succ;
          last (apply Z.min_glb; omega).
          rewrite Z2Nat.id; auto.
          cut (0 ≤ Z.min c MAX); intros; try (apply Z.min_glb); omega.
        * apply ip_coupling_mret.
          split; auto => //=.
      - eexists. split; last first.
        { rewrite -List.map_cons. 
          eapply in_map_iff.
          exists (mret (Z.to_nat (Z.min c MAX))); split.
          * reflexivity.
          * rewrite -map_cons. eapply in_map_iff.
            exists (Z.to_nat (Z.min c MAX)); split; auto.
            replace (O :: iota 1 MAX) with (iota O (S MAX - 0)); last first.
            { rewrite //=.  }
            apply Iter.In_iota; split.
            **  omega. 
            ** rewrite Z2Nat.inj_min.
               etransitivity; first apply Min.le_min_r.
               rewrite //=. 
               rewrite Nat2Z.id.
               reflexivity.
        }
        setoid_rewrite pidist_left_id. reflexivity.
    }
    rewrite //= in HR. (* destruct HR as (Heqz&?); subst. *)
    destruct b.
    * iMod (own_update_2 with "Hγp' Hγp") as "[Hγp' Hγp]".
      { apply frac_auth_update, (nat_local_update _ _ (np_global) (np)); omega. }
      iMod (own_update_2 with "Hγv' Hγv") as "[Hγv' Hγv]".
      { apply frac_auth_update, (nat_local_update _ _ (nv_global + z') (nc + z')); omega. }
      iMod ("Hclose" with "[Hγp' Hγv' Hprob]").
      { iNext. iExists np_global, (nv_global + z')%nat. iFrame.
        iRight. iFrame. }

      iModIntro.
      wp_let.
      wp_if.
      wp_op.
      wp_bind (FAA _ _).
      iInv N1 as (c') ">[Hγl' Hl]" "Hclose".
      wp_faa.
      iMod (own_update_2 with "Hγl' Hγl") as "[Hγl' Hγl]".
      { apply frac_auth_update, (nat_local_update _ _ (c' + z') (nc + z')); omega. }

      iMod ("Hclose" with "[Hγl' Hl]").
      { iNext. iExists (c' + z')%nat. iFrame.
        rewrite ?Nat2Z.inj_add => //=.
        rewrite HR. rewrite Zplus_comm. done.
      }

      iModIntro. wp_let.
      iApply "HΦ".
      iExists (nc + z')%nat.
      iFrame.
    * replace (nv_global + z')%nat with (nv_global); last first.
      { apply Z_of_nat_inj. rewrite Nat2Z.inj_add HR. omega. }
      iMod (own_update_2 with "Hγp' Hγp") as "[Hγp' Hγp]".
      { apply frac_auth_update, (nat_local_update _ _ (np_global) (np)); omega. }
      iMod ("Hclose" with "[Hγp' Hγv' Hprob]").
      { iNext. iExists np_global, nv_global. iFrame. iRight. iFrame. }

      iModIntro.
      wp_let.
      wp_if.

      iApply "HΦ".
      iExists nc. iFrame.
Qed.

Lemma read_spec N1 N2 γl γp γv l nc:
  N1 ## N2 →
  {{{ inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv γp γv) ∗
      acounter γl γp γv 1 0 nc }}}
    read (Lit $ LitLoc l) 
  {{{ (v : nat), RET LitV $ LitInt v; ownProb (mret v) }}}. 
Proof.
  iIntros (Hdisjoint Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(#Hinv1&#Hinv2&(Hγp&Hγl&Hγv))".
  wp_let. 
  iInv N1 as (c) ">[Hγl' Hl]" "Hclose1".
  iInv N2 as (np_global nv_global) ">(Hγp'&Hγv'&Hprob)" "Hclose2".
  iDestruct "Hprob" as "[Hbad|Hprob]".
  { iDestruct (own_valid_2 with "Hbad Hγp") as %?%frac_auth_frag_valid_op_1_l; done. }
  wp_load.
  iDestruct (own_valid_2 with "Hγp' Hγp") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγl' Hγl") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγv' Hγv") as % ->%frac_auth_agreeL.
  iMod ("Hclose2" with "[Hγp' Hγv' Hγp]").
  { iNext. iExists O, nc. iFrame. iLeft. iFrame. }

  iModIntro. 
  iMod ("Hclose1" with "[Hγl' Hl]"). 
  { iNext. iExists nc. iFrame. }

  iModIntro. iApply "HΦ". rewrite //=.
Qed.

Lemma newcounter_spec N1 N2 n :
  {{{ ownProb (approx_n n O)}}}
    newcounter #()
  {{{ γl γp γv l, RET #l;
      inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv γp γv) ∗
     acounter γl γp γv 1 n O }}}.
Proof.
  iIntros (Φ) "Hprob HΦ".
  iMod (own_alloc (●! O%nat ⋅ ◯! O%nat)) as (γl) "[Hγl' Hγl]"; first done.
  iMod (own_alloc (●! n%nat ⋅ ◯! n%nat)) as (γp) "[Hγp' Hγp]"; first done.
  iMod (own_alloc (●! O%nat ⋅ ◯! O%nat)) as (γv) "[Hγv' Hγv]"; first done.

  rewrite -wp_fupd /newcounter /=.
  wp_let. wp_alloc l as "Hl".
  iMod (inv_alloc N1 _ (acounter_loc_inv γl l) with "[Hl Hγl']").
  { iNext. iExists O. iFrame. }
  iMod (inv_alloc N2 _ (acounter_prob_inv γp γv) with "[Hγp' Hγv' Hprob]").
  { iNext. iExists n, O. iFrame. iRight. done. }

  iApply "HΦ".
  iModIntro. iFrame.
Qed.

(* Bundled versions to match cleaner formulation for paper *)
Definition Acounter γl γp γc l (q : frac) (nperm : nat) : iProp Σ :=
  (∃ N1 N2 ncontrib,
  ⌜ N1 ## N2 ⌝ ∗ inv N1 (acounter_loc_inv γl l) ∗ inv N2 (acounter_prob_inv γp γc) ∗
    own γp (◯!{q} nperm) ∗ own γl (◯!{q} ncontrib) ∗ own γc (◯!{q} ncontrib))%I.

Lemma Acounter_sep γl γp γv l q1 q2 np1 np2:
  Acounter γl γp γv l (q1 + q2) (np1 + np2) ⊢
           Acounter γl γp γv l q1 np1 ∗ Acounter γl γp γv l q2 np2.
Proof.
  iStartProof. 
  * iIntros "HA".
    iDestruct "HA" as (N1 N2 nc) "(%&#Hi1&#Hi2&HA)".
    replace nc with (O + nc)%nat by auto.
    iPoseProof (acounter_sep γl γp γv q1 q2 np1 np2 O nc with "[HA]") as "(HA1&HA2)"; auto.
    iSplitL "HA1".
    ** iExists N1, N2, O. auto.
    ** iExists N1, N2, nc. auto.
Qed.

Lemma Acounter_join γl γp γv l q1 q2 np1 np2:
  Acounter γl γp γv l q1 np1 ∗ Acounter γl γp γv l q2 np2 ⊢
           Acounter γl γp γv l (q1 + q2) (np1 + np2).
Proof.
  iStartProof.
  iIntros "(HA1&HA2)".
  iDestruct "HA1" as (N1 N2 nc1) "(%&#Hi1&#Hi2&HA1)".
  iDestruct "HA2" as (N1' N2' nc2) "(%&#Hi1'&#Hi2'&HA2)".
  iCombine "HA1" "HA2" as "HA".
  rewrite acounter_join. 
  iExists N1, N2, (nc1 + nc2)%nat; auto.
Qed.

Lemma newcounter_spec' n :
  {{{ ownProb (approx_n n O)}}}
    newcounter #()
  {{{ γl γp γc l, RET #l;
     Acounter γl γp γc l 1 n}}}.
Proof.
  iIntros (Φ) "Hprob HΦ".
  set (N1 := nroot .@ "N1").
  set (N2 := nroot .@ "N2").
  iApply (newcounter_spec N1 N2 n with "Hprob").
  iNext. iIntros (γl γp γv l) "(Hinv1&Hinv2&Hacounter)". iApply "HΦ".
  iExists N1, N2, O.
  iFrame. rewrite /N1/N2; eauto with *.
Qed.

Lemma incr_spec' γl γp γc l q np :
  {{{ Acounter γl γp γc l q (S np)}}}
    incr (Lit $ LitLoc l)
  {{{ RET LitV LitUnit; Acounter γl γp γc l q np }}}.
Proof.
  iIntros (Φ) "Hacounter HΦ".
  iDestruct "Hacounter" as (N1 N2 ncontrib) "(%&#Hinv1&#Hinv2&H)".
  iApply (incr_spec with "[H]").
  { iFrame "Hinv1 Hinv2 H". }
  iNext. iIntros "HA". iDestruct "HA" as (nc') "HA".
  iApply "HΦ".
  iExists N1, N2, nc'; iFrame; eauto.
Qed.

Lemma read_spec' γl γp γc l:
  {{{ Acounter γl γp γc l 1 0}}}
    read (Lit $ LitLoc l)
  {{{ (v : nat), RET LitV $ LitInt v; ownProb (mret v) }}}.
Proof.
  iIntros (Φ) "Hacounter HΦ".
  iDestruct "Hacounter" as (N1 N2 ncontrib) "(%&#Hinv1&#Hinv2&H)".
  iApply (read_spec with "[H]"); first by eauto.
  { iFrame "Hinv1 Hinv2 H". }
  done.
Qed.


Section simple_client.

Definition incr_n : val :=
  rec: "incr_n" "l" "n" :=
    if: "n" = #0 then
      #()
    else
      incr "l";;
      let: "n'" := "n" - #1 in
      "incr_n" "l" "n'".
      
Definition simple_client n1 n2 : expr := 
  let: "l" := newcounter #() in
  (incr_n "l" #n1  ||| incr_n "l" #n2) ;;
  read "l".

Lemma incr_n_spec N1 N2 γl γp γv q n1 n2 l:
  {{{ inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv γp γv) ∗
      acounter γl γp γv q n1 n2 }}}
    (incr_n #l) #n1
  {{{ v, RET v; ∃ nc : nat, acounter γl γp γv q 0 nc }}}.
Proof.
  iIntros (Φ) "(#Hinv1&#Hinv2&Hcounter) Hwand". 
  iRevert (n1 n2) "Hcounter".
  iLöb as "IH". iIntros (n1 n2) "Hcounter".
  wp_rec.
  wp_let.
  wp_op; case_bool_decide.
  * wp_if.
    assert (n1 = 0)%nat by (inversion H; auto; omega).
    subst. iApply "Hwand". iExists n2. done.
  * wp_if.
    assert (n1 ≠ 0)%nat.
    { intros Heq.  subst. rewrite //= in H. }
    destruct n1 as [| n1]; first by auto.
    wp_apply (incr_spec with "[Hcounter]"); [ iFrame "Hinv1 Hinv2"; done |].
    iIntros "Hcounter".
    iDestruct "Hcounter" as (nc) "Hcounter".
    wp_let. rewrite Zpos_P_of_succ_nat. wp_op.
    replace (Z.succ n1 - 1)%Z with (n1 : Z) by omega.
    wp_let. wp_apply ("IH" with "Hwand Hcounter").
Qed.

Lemma incr_n_spec' γl γp γc l q n1:
  {{{ Acounter γl γp γc l q n1}}}
    (incr_n #l) #n1
  {{{ v, RET v; Acounter γl γp γc l q 0 }}}.
Proof.
  iIntros (Φ) "Hacounter HΦ".
  iDestruct "Hacounter" as (N1 N2 nc) "(%&#Hinv1&#Hinv2&H)".
  iApply (incr_n_spec with "[H]").
  { iFrame "Hinv1 Hinv2 H". }
  iNext. iIntros (v) "HA". iDestruct "HA" as (nc') "HA".
  iApply "HΦ".
  iExists N1, N2, nc'; iFrame; eauto.
Qed.
  
Lemma simple_client_spec n1 n2:
  ownProb (approx_n (n1 + n2) O) ⊢
          WP (simple_client n1 n2) {{ v, ∃ (v' : nat), ownProb (mret v') ∗
                                                 ⌜ v = LitV $ LitInt v' ⌝ }}%I.
Proof.
  iIntros "Hprob". rewrite /simple_client.
  wp_bind (newcounter _).
  wp_apply (newcounter_spec' with "Hprob").
  iIntros (γl γp γv l) "Hcounter".
  rewrite -(Qp_div_2 1).
  replace 0%nat with (0 + 0)%nat by auto.
  rewrite Acounter_sep.
  iDestruct "Hcounter" as "(Hcounter1&Hcounter2)".
  wp_let. wp_apply (wp_par (λ v, Acounter γl γp γv l (1 / 2)%Qp 0)%I
                           (λ v, Acounter γl γp γv l (1 / 2)%Qp 0)%I
                      with "[Hcounter1] [Hcounter2]").
  - wp_apply (incr_n_spec' with "Hcounter1").
    iIntros (_); auto.
  - wp_apply (incr_n_spec' with "Hcounter2").
    iIntros (_); auto.
  - iIntros (v1 v2) "(Hpost1&Hpost2)".
    iCombine "Hpost1" "Hpost2" as "Hpost".
    rewrite Acounter_join Qp_div_2 //=.
    iNext. wp_let. wp_apply (read_spec' with "Hpost"); eauto.
Qed.
End simple_client.


Section list_client.

  (* Convert a list of Coq bools into a heap_lang tuple *)
Fixpoint l2tuple (l: list bool) : val :=
  match l with
  | [] => NONEV
  | b :: l =>
    SOMEV (#b, l2tuple l)
  end.

Definition foldLeft : val :=
  rec: "foldLeft" "f" "l" "a" :=
    match: "l" with
      NONE => "a"
    | SOME "cell" =>
      "foldLeft" "f" (Snd "cell") ("f" "a" (Fst "cell"))
    end.

(* Uses the approx counter to count the number of trues occurring in a list *)
Definition countTrue : val := 
  λ: "c" "lb",
  foldLeft (λ: <> "b", if: "b" then incr "c" else #()) "lb" #().

Definition list_client l1 l2 : expr := 
  let: "c" := newcounter #() in
  (countTrue "c" (l2tuple l1)  ||| countTrue "c" (l2tuple l2)) ;;
  read "c".

Definition lenTrue l := (List.length (List.filter (λ x, x) l)).

Lemma countTrue_spec γl γp γc l q lb:
  {{{ Acounter γl γp γc l q (lenTrue lb) }}}
    (countTrue #l) (l2tuple lb)
  {{{ v, RET v; Acounter γl γp γc l q 0 }}}.
Proof.
  iIntros (Φ) "HA Hwand". 
  wp_let. wp_let. wp_let. wp_let. wp_let.
  iRevert (lb) "HA".
  iLöb as "IH". iIntros (lb) "Hcounter".
  destruct lb.
  * wp_match. iApply "Hwand"; done.
  * rewrite /l2tuple -/l2tuple.
    wp_match. wp_let. wp_proj.
    wp_let. wp_let. wp_proj. wp_let.
    destruct b.
    ** wp_if. wp_apply (incr_spec' with "Hcounter").
       iIntros "Hcounter".
       wp_let.  iApply ("IH" with "Hwand Hcounter").
    ** wp_if.
       wp_let.  iApply ("IH" with "Hwand [Hcounter]").
       rewrite //=.
Qed.

Lemma list_client_spec l1 l2:
  ownProb (approx_n (lenTrue l1 + lenTrue l2) O) ⊢
          WP (list_client l1 l2) {{ v, ∃ (v' : nat), ownProb (mret v') ∗
                                                 ⌜ v = LitV $ LitInt v' ⌝ }}%I.
Proof.
  iIntros "Hprob". rewrite /list_client.
  wp_bind (newcounter _).
  wp_apply (newcounter_spec' with "Hprob").
  iIntros (γl γp γv l) "Hcounter".
  rewrite -(Qp_div_2 1).
  replace 0%nat with (0 + 0)%nat by auto.
  rewrite Acounter_sep.
  iDestruct "Hcounter" as "(Hcounter1&Hcounter2)".
  wp_let. wp_apply (wp_par (λ v, Acounter γl γp γv l (1 / 2)%Qp 0)%I
                           (λ v, Acounter γl γp γv l (1 / 2)%Qp 0)%I
                      with "[Hcounter1] [Hcounter2]").
  - wp_apply (countTrue_spec with "Hcounter1").
    iIntros (_); auto.
  - wp_apply (countTrue_spec with "Hcounter2").
    iIntros (_); auto.
  - iIntros (v1 v2) "(Hpost1&Hpost2)".
    iCombine "Hpost1" "Hpost2" as "Hpost".
    rewrite Acounter_join Qp_div_2 //=.
    iNext. wp_let. wp_apply (read_spec' with "Hpost"); eauto.
Qed.
End list_client.


End proof.


Section adequate.
Let Σ : gFunctors := #[ heapΣ ; spawnΣ; acounterΣ].

Definition client_ival sch e σ k := @ivdist_tpool_stepN heap_ectxi_lang sch [e] σ k.

Lemma generic_client_adequate n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0) -∗
   WP e {{ v, ∃ v' : nat, ownProb (mret v') ∗ ⌜v = #v'⌝ }})%I →
  terminates sch [([e], σ)] k →
  irrel_couplingP (client_ival sch e σ k)
                  (approx_n n O)
                  (prob_adequacy.coupling_post (λ x y, x = LitV $ LitInt y)).
Proof.
  intros Hspec ?.
  eapply (heap_prob_adequacy Σ (approx_n n 0)
                             e σ (λ x y, x = LitV $ LitInt y) sch k); eauto.
  intros. iIntros "Hprob".
  iApply Hspec; done.
Qed.

Lemma generic_client_ex_Ex_ival n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0) -∗
   WP e {{ v, ∃ v' : nat, ownProb (mret v') ∗ ⌜v = #v'⌝ }})%I →
  terminates sch [([e], σ)] k →
  ex_Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (LitV (LitInt y)) => IZR y
                            | _ => 0
                            end
                end) (client_ival sch e σ k).
Proof.
  intros. 
  intros. eapply irrel_coupling_eq_ex_Ex_supp; last first.
  { eapply pspec_bounded.  eexists. apply approx_n_bounded. }
    eapply irrel_coupling_conseq; last first.
    * eapply irrel_coupling_proper; last eapply generic_client_adequate.
      ** reflexivity.
      ** reflexivity. 
      ** eauto.
      ** eauto.
    * intros x y.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=. destruct l0 => //=.
      inversion 1. subst.
      rewrite INR_IZR_INZ. done.
Qed.

Lemma generic_client_Ex_ival n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0) -∗
   WP e {{ v, ∃ v' : nat, ownProb (mret v') ∗ ⌜v = #v'⌝ }})%I →
  terminates sch [([e], σ)] k →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (LitV (LitInt y)) => IZR y
                            | _ => 0
                            end
                end) (client_ival sch e σ k)
  = INR n%nat.  
Proof.
  intros. replace (INR n) with (INR (n + 0)%nat) by (f_equal; omega).
  apply stochastic_order.Finite_inj.
  apply Rbar_le_antisym.
  - rewrite -Ex_max_approx_n.
    intros. apply irrel_coupling_eq_Ex_max_supp.
    eapply irrel_coupling_conseq; last first.
    * eapply irrel_coupling_proper; last eapply generic_client_adequate.
      ** reflexivity.
      ** reflexivity. 
      ** eauto.
      ** eauto.
    * intros x y.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=. destruct l0 => //=.
      inversion 1. subst.
      rewrite INR_IZR_INZ. done.
    * apply pspec_bounded. eexists. apply approx_n_bounded.
  - rewrite -Ex_min_approx_n.
    intros. apply irrel_coupling_eq_Ex_min_supp.
    eapply irrel_coupling_conseq; last first.
    * eapply irrel_coupling_proper; last eapply generic_client_adequate.
      ** reflexivity.
      ** reflexivity. 
      ** eauto.
      ** eauto.
    * intros x y.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=. destruct l0 => //=.
      inversion 1. subst.
      rewrite INR_IZR_INZ. done.
    * apply pspec_bounded. eexists. apply approx_n_bounded.
Qed.

Lemma simple_client_ex_Ex_ival (n1 n2: nat) sch σ k:
  terminates sch [([simple_client n1 n2], σ)] k →
  ex_Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (LitV (LitInt y)) => IZR y
                            | _ => 0
                            end
                end) (client_ival sch (simple_client n1 n2) σ k).
Proof.
  eapply generic_client_ex_Ex_ival.
  iIntros; iApply simple_client_spec; done.
Qed.

Lemma simple_client_Ex_ival (n1 n2: nat) sch σ k:
  terminates sch [([simple_client n1 n2], σ)] k →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (LitV (LitInt y)) => IZR y
                            | _ => 0
                            end
                end) (client_ival sch (simple_client n1 n2) σ k)
  = INR (n1 + n2)%nat.  
Proof.
  apply generic_client_Ex_ival.
  iIntros; iApply simple_client_spec; done.
Qed.

Lemma list_client_Ex_ival lb1 lb2 sch σ k:
  terminates sch [([list_client lb1 lb2], σ)] k →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (LitV (LitInt y)) => IZR y
                            | _ => 0
                            end
                end) (client_ival sch (list_client lb1 lb2) σ k)
  = INR (lenTrue lb1 + lenTrue lb2)%nat.  
Proof.
  apply generic_client_Ex_ival.
  iIntros; iApply list_client_spec; done.
Qed.

End adequate.
End COUNTER.