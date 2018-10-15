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

Fixpoint approx_n (n: nat) (tot: nat) (l: nat) : pidist (nat * nat) :=
  match n with
  | O => mret (tot, l)
  | S n' =>
    pidist_union (mret (tot, l))
                 (x ← approx_incr; approx_n n' (S tot) (l + x))
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
  pspec (approx_incr) (λ x : nat, x <= S MAX)%nat.
Proof.
  eapply (pspec_mbind _ _ (λ x, x <= MAX)%nat); first eapply select_upto_spec1.
  intros a Hle. rewrite /flip_incr.
  apply pspec_pidist_plus.
  * apply pspec_mret. omega.
  * apply pspec_mret. omega.
Qed.

Lemma approx_incr_bounded':
  pspec (approx_incr) (λ x : nat, Rabs (INR x) <= INR (S MAX)).
Proof.
  eapply pspec_conseq; first eapply approx_incr_bounded.
  intros a Hle%le_INR. rewrite Rabs_right //=.
  apply Rle_ge, pos_INR.
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

Lemma approx_n_bounded_incr n curr:
  (curr <= approx_n_bound n curr)%nat.
Proof.
  revert curr.
  induction n => //=.
  intros curr.
  etransitivity; first eapply IHn. eapply approx_n_bounded_mono; omega.
Qed.

Lemma approx_n_bounded n tot curr:
  pspec (approx_n n tot curr)
        (λ x : nat * nat, fst x <= (n + tot) ∧ snd x <= approx_n_bound n curr)%nat.
Proof.
  revert tot curr.
  induction n => tot curr.
  - apply pspec_mret => //=. 
  - rewrite /=. apply pspec_union.
    * apply pspec_mret => //=; split; try omega.
      etransitivity; first eapply approx_n_bounded_incr.
      eapply approx_n_bounded_mono; omega.
    * eapply pspec_mbind; first eapply approx_incr_bounded.
    intros a Hle.
    eapply pspec_conseq; first eapply IHn => //=.
    intros k => //=.
    intros (?&?). split; first by omega.
    etransitivity; first eassumption. 
    apply approx_n_bounded_mono.
    rewrite //= in Hle. omega.
Qed.

Lemma approx_n_bounded_diff n tot curr:
  pspec (approx_n n tot curr)
        (λ x : nat * nat, Rabs (INR (fst x) - INR (snd x)) <= (INR (n + tot)) +
                                                              (INR (approx_n_bound n curr))).
Proof.
  eapply pspec_conseq; first eapply approx_n_bounded.
  intros (res&curr') => //=.
  intros (Hle1&Hle2).
  rewrite /Rminus.
  setoid_rewrite  Rabs_triang.
  apply Rplus_le_compat.
  * rewrite Rabs_right; last apply Rle_ge, pos_INR.
    apply le_INR. auto.
  * rewrite Rabs_Ropp Rabs_right; last apply Rle_ge, pos_INR.
    apply le_INR. auto.
Qed.

Import Rbar.

Lemma Ex_min_approx_incr:
  Ex_min INR (approx_incr) = Finite 1.
Proof.
  rewrite /approx_incr.
  apply Ex_min_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S MAX)).
    apply approx_incr_bounded'.
  }
  intros k. rewrite /flip_incr.
  rewrite ?Ex_min_pidist_plus ?Ex_min_mret // ?(S_INR) //=.
  * rewrite //= Rmult_0_r Rplus_0_r. 
    specialize (INRp1_prob k); intros (?&?).
    specialize (Rcomplements.INRp1_pos k). intros.
    f_equal. field. nra.
  * apply ex_Ex_extrema_pidist_plus; apply ex_Ex_extrema_mret.
Qed.

Lemma Ex_max_approx_incr :
  Ex_max INR (approx_incr) = Finite 1.
Proof.
  rewrite /approx_incr.
  apply Ex_max_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S MAX)).
    apply approx_incr_bounded'.
  }
  intros k. rewrite /flip_incr.
  rewrite ?Ex_max_pidist_plus ?Ex_max_mret // ?(S_INR) //=.
  * rewrite //= Rmult_0_r Rplus_0_r. 
    specialize (INRp1_prob k); intros (?&?).
    specialize (Rcomplements.INRp1_pos k). intros.
    f_equal. field. nra.
  * apply ex_Ex_extrema_pidist_plus; apply ex_Ex_extrema_mret.
Qed.
   
Lemma Ex_min_approx_n (n: nat) tot l:
  Ex_min (λ x : nat * nat, INR (fst x) - INR (snd x)) (approx_n n tot l) =
  Finite (INR tot - INR l).
Proof.
  revert tot l.
  induction n => tot l.
  - rewrite //=. rewrite Ex_min_mret. done.
  - rewrite Ex_min_pidist_union -/approx_n. apply Rbar_min_case.
    { rewrite Ex_min_mret. done. }
    transitivity (Ex_min (λ x : nat, INR (S tot) - INR (l + x)) (approx_incr)).
    { rewrite Ex_min_bind_post -/approx_n.
      * apply Ex_min_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
      * apply Ex_min_bounded_supp_fun_finite.
        apply pspec_bounded. 
        exists ((INR (S tot)) + (INR (l + MAX + 1))).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn.
        rewrite /Rminus. setoid_rewrite Rabs_triang.
        apply Rplus_le_compat.
        ** rewrite Rabs_right; last apply Rle_ge, pos_INR. by right. 
        ** rewrite Rabs_Ropp. rewrite Rabs_right; last apply Rle_ge, pos_INR. 
           apply le_INR. rewrite //= in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (S n + tot) + (INR (approx_n_bound (S n) l))).
        eapply pspec_union_inv_r, (approx_n_bounded_diff (S n) tot l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded.
        exists (INR (S tot) + INR (l + S MAX)).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros k Hb. rewrite IHn.
        rewrite /Rminus. setoid_rewrite Rabs_triang.
        apply Rplus_le_compat.
        ** rewrite Rabs_right; last apply Rle_ge, pos_INR. by right. 
        ** rewrite Rabs_Ropp. rewrite Rabs_right; last apply Rle_ge, pos_INR. 
           apply le_INR. rewrite //= in Hb. omega.
    }
    rewrite Ex_min_plus_const_l.
    rewrite ?plus_INR.
    setoid_rewrite plus_INR.
    rewrite -(Rbar_opp_involutive (Ex_min _ _)).
    setoid_rewrite Ropp_plus_distr.
    rewrite Ex_min_plus_const_l.
    rewrite S_INR //=.
    rewrite Rbar_opp_involutive.
    rewrite //=.
    rewrite -(Rbar_opp_involutive (Ex_min _ _)).
    rewrite -Ex_max_neg_min Ex_max_approx_incr //=.
    f_equal. nra.
Qed.

Lemma Ex_max_approx_n (n: nat) tot l:
  Ex_max (λ x : nat * nat, INR (fst x) - INR (snd x)) (approx_n n tot l) =
  Finite (INR tot - INR l).
Proof.
  revert tot l.
  induction n => tot l.
  - rewrite //=. rewrite Ex_max_mret. done.
  - rewrite Ex_max_pidist_union -/approx_n. apply Reals_ext.Rbar_max_case.
    { rewrite Ex_max_mret. done. }
    transitivity (Ex_max (λ x : nat, INR (S tot) - INR (l + x)) (approx_incr)).
    { rewrite Ex_max_bind_post -/approx_n.
      * apply Ex_max_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
      * apply Ex_max_bounded_supp_fun_finite.
        apply pspec_bounded. 
        exists ((INR (S tot)) + (INR (l + MAX + 1))).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn.
        rewrite /Rminus. setoid_rewrite Rabs_triang.
        apply Rplus_le_compat.
        ** rewrite Rabs_right; last apply Rle_ge, pos_INR. by right. 
        ** rewrite Rabs_Ropp. rewrite Rabs_right; last apply Rle_ge, pos_INR. 
           apply le_INR. rewrite //= in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (S n + tot) + (INR (approx_n_bound (S n) l))).
        eapply pspec_union_inv_r, (approx_n_bounded_diff (S n) tot l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded.
        exists (INR (S tot) + INR (l + S MAX)).
        eapply pspec_conseq; first eapply approx_incr_bounded.
        intros k Hb. rewrite IHn.
        rewrite /Rminus. setoid_rewrite Rabs_triang.
        apply Rplus_le_compat.
        ** rewrite Rabs_right; last apply Rle_ge, pos_INR. by right. 
        ** rewrite Rabs_Ropp. rewrite Rabs_right; last apply Rle_ge, pos_INR. 
           apply le_INR. rewrite //= in Hb. omega.
    }
    rewrite Ex_max_plus_const_l.
    setoid_rewrite plus_INR.
    rewrite -(Rbar_opp_involutive (Ex_max _ _)).
    setoid_rewrite Ropp_plus_distr.
    rewrite Ex_max_plus_const_l.
    rewrite S_INR //=.
    rewrite Rbar_opp_involutive.
    rewrite //=.
    rewrite Ex_max_neg_min.
    setoid_rewrite Ropp_involutive.
    rewrite Ex_min_approx_incr //=.
    f_equal. nra.
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

Definition acounter_prob_inv (max : nat) (γp γv : gname): iProp Σ :=
  (∃ n1 n2, ⌜ (n1 ≤ max)%nat ⌝ ∗ own γp (●! n1) ∗ own γv (●! n2) ∗
                (own γp (◯! n1) ∨ ownProb (approx_n n1 (max - n1) n2)))%I.

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

Lemma incr_spec N1 N2 γl γp γv l q max np nc:
  {{{ inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv max γp γv) ∗
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
  iInv N2 as (np_global nv_global) ">(%&Hγp'&Hγv'&Hprob)" "Hclose".
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
    rewrite H0. destruct (INRp1_prob (Z.to_nat (Z.min c MAX))).
    split; auto; etransitivity; eauto; rewrite plus_INR //=.
  }

  iPoseProof (ownProb_anti with "Hprob") as "Hprob".
  { rewrite pidist_union_comm. apply pidist_union_le. }

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
        iSplitL ""; first (iPureIntro; omega).
        iRight. replace (S (max - S np_global)) with (max - np_global)%nat; first iFrame.
        omega. }

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
      { iNext. iExists np_global, nv_global. iFrame.
        iSplitL ""; first (iPureIntro; omega).
        iRight. replace (S (max - S np_global)) with (max - np_global)%nat; first iFrame.
        omega. }

      iModIntro.
      wp_let.
      wp_if.

      iApply "HΦ".
      iExists nc. iFrame.
Qed.

Lemma read_spec N1 N2 γl γp γv l max np nc:
  N1 ## N2 →
  {{{ inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv max γp γv) ∗
      acounter γl γp γv 1 np nc }}}
    read (Lit $ LitLoc l) 
  {{{ (v : nat), RET LitV $ LitInt v; ownProb (mret (max - np, v))%nat }}}. 
Proof.
  iIntros (Hdisjoint Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(#Hinv1&#Hinv2&(Hγp&Hγl&Hγv))".
  wp_let. 
  iInv N1 as (c) ">[Hγl' Hl]" "Hclose1".
  iInv N2 as (np_global nv_global) ">(%&Hγp'&Hγv'&Hprob)" "Hclose2".
  iDestruct "Hprob" as "[Hbad|Hprob]".
  { iDestruct (own_valid_2 with "Hbad Hγp") as %?%frac_auth_frag_valid_op_1_l; done. }
  wp_load.
  iDestruct (own_valid_2 with "Hγp' Hγp") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγl' Hγl") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγv' Hγv") as % ->%frac_auth_agreeL.
  iMod ("Hclose2" with "[Hγp' Hγv' Hγp]").
  { iNext. iExists np, nc. iFrame.
    iSplitL ""; first by (iPureIntro).
    iLeft. iFrame. }

  iModIntro. 
  iMod ("Hclose1" with "[Hγl' Hl]"). 
  { iNext. iExists nc. iFrame. }

  iModIntro. iApply "HΦ". rewrite //=.
  iApply (ownProb_anti with "Hprob").
  destruct np.
  * reflexivity.
  * rewrite //=. apply pidist_union_le. 
Qed.

Lemma newcounter_spec N1 N2 n :
  {{{ ownProb (approx_n n O O)}}}
    newcounter #()
  {{{ γl γp γv l, RET #l;
      inv N1 (acounter_loc_inv γl l) ∗
      inv N2 (acounter_prob_inv n γp γv) ∗
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
  iMod (inv_alloc N2 _ (acounter_prob_inv n γp γv) with "[Hγp' Hγv' Hprob]").
  { iNext. iExists n, O. iFrame. iSplitL ""; auto. iRight.
    replace (n - n)%nat with O by omega. done. }

  iApply "HΦ".
  iModIntro. iFrame.
Qed.

(* Bundled versions to match cleaner formulation for paper *)
Definition Acounter max γl γp γc l (q : frac) (nperm : nat) : iProp Σ :=
  (∃ N1 N2 ncontrib,
  ⌜ N1 ## N2 ⌝ ∗ inv N1 (acounter_loc_inv γl l) ∗ inv N2 (acounter_prob_inv max γp γc) ∗
    own γp (◯!{q} nperm) ∗ own γl (◯!{q} ncontrib) ∗ own γc (◯!{q} ncontrib))%I.

Lemma Acounter_sep max γl γp γv l q1 q2 np1 np2:
  Acounter max γl γp γv l (q1 + q2) (np1 + np2) ⊢
           Acounter max γl γp γv l q1 np1 ∗ Acounter max γl γp γv l q2 np2.
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

Lemma Acounter_join max γl γp γv l q1 q2 np1 np2:
  Acounter max γl γp γv l q1 np1 ∗ Acounter max γl γp γv l q2 np2 ⊢
           Acounter max γl γp γv l (q1 + q2) (np1 + np2).
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
  {{{ ownProb (approx_n n O O)}}}
    newcounter #()
  {{{ γl γp γc l, RET #l;
     Acounter n γl γp γc l 1 n}}}.
Proof.
  iIntros (Φ) "Hprob HΦ".
  set (N1 := nroot .@ "N1").
  set (N2 := nroot .@ "N2").
  iApply (newcounter_spec N1 N2 n with "Hprob").
  iNext. iIntros (γl γp γv l) "(Hinv1&Hinv2&Hacounter)". iApply "HΦ".
  iExists N1, N2, O.
  iFrame. rewrite /N1/N2; eauto with *.
Qed.

Lemma incr_spec' max γl γp γc l q np :
  {{{ Acounter max γl γp γc l q (S np)}}}
    incr (Lit $ LitLoc l)
  {{{ RET LitV LitUnit; Acounter max γl γp γc l q np }}}.
Proof.
  iIntros (Φ) "Hacounter HΦ".
  iDestruct "Hacounter" as (N1 N2 ncontrib) "(%&#Hinv1&#Hinv2&H)".
  iApply (incr_spec with "[H]").
  { iFrame "Hinv1 Hinv2 H". }
  iNext. iIntros "HA". iDestruct "HA" as (nc') "HA".
  iApply "HΦ".
  iExists N1, N2, nc'; iFrame; eauto.
Qed.

Lemma read_spec' max γl γp γc l np:
  {{{ Acounter max γl γp γc l 1 np}}}
    read (Lit $ LitLoc l)
  {{{ (v : nat), RET LitV $ LitInt v; ownProb (mret (max - np, v)%nat) }}}.
Proof.
  iIntros (Φ) "Hacounter HΦ".
  iDestruct "Hacounter" as (N1 N2 ncontrib) "(%&#Hinv1&#Hinv2&H)".
  iApply (read_spec with "[H]"); first by eauto.
  { iFrame "Hinv1 Hinv2 H". }
  done.
Qed.


Section nondet_list_client.

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

Definition lenTrue l := (List.length (List.filter (λ x, x) l)).

Lemma countTrue_spec max γl γp γc l q np lb:
  {{{ ⌜ (lenTrue lb ≤ np)%nat ⌝ ∗ Acounter max γl γp γc l q np }}}
    (countTrue #l) (l2tuple lb)
  {{{ v, RET v; Acounter max γl γp γc l q (np - lenTrue lb) }}}.
Proof.
  iIntros (Φ) "HA Hwand". 
  wp_let. wp_let. wp_let. wp_let. wp_let.
  iRevert (np lb) "HA Hwand".
  iLöb as "IH". iIntros (np lb) "(Hpure&Hcounter) Hwand".
  iDestruct "Hpure" as %Hle.
  destruct lb.
  * wp_match. iApply "Hwand". rewrite /lenTrue//=. replace (np - 0)%nat with np by omega.
    done.
  * rewrite /l2tuple -/l2tuple.
    wp_match. wp_let. wp_proj.
    wp_let. wp_let. wp_proj. wp_let.
    destruct b.
    ** destruct np.
       { exfalso. rewrite /lenTrue//= in Hle. omega. }
       wp_if.
       wp_apply (incr_spec' with "Hcounter").
       iIntros "Hcounter".
       wp_let.  iApply ("IH" with "[Hcounter] [Hwand]").
       { iFrame.  iPureIntro. rewrite /lenTrue//= in Hle *. omega. }
       iIntros (v). iSpecialize ("Hwand" $! v).
       replace (S np - lenTrue (true :: lb))%nat with (np - lenTrue lb)%nat; first iFrame.
       { rewrite /lenTrue//=. }
    ** wp_if.
       wp_let.  iApply ("IH" with "[Hcounter] [Hwand]").
       { iFrame.  iPureIntro. rewrite /lenTrue//= in Hle *. }
       rewrite //=.
Qed.

Variable list_gen : expr.
Variable max_length : nat.
Variable list_gen_spec:
  (WP list_gen {{ v, ∃ v1 v2 l1 l2, ⌜ v = PairV (LitV $ LitInt (lenTrue l1 + lenTrue l2))
                                                      (PairV v1 v2)
                                          ∧ l2tuple l1 = v1
                                          ∧ l2tuple l2 = v2
                                          ∧ (lenTrue l1 + lenTrue l2 ≤ max_length)%nat ⌝}})%I.

Definition list_client : expr :=
  let: "lc" := list_gen in
  let: "c" := newcounter #() in
  let: "t" := Fst "lc" in
  let: "l1" := Fst (Snd "lc") in
  let: "l2" := Snd (Snd "lc") in
  (countTrue "c"  "l1" ||| countTrue "c" "l2") ;;
  ("t", read "c").

Lemma list_client_spec :
  ownProb (approx_n max_length O O) ⊢
          WP list_client {{ v, ∃ v' : nat * nat, ownProb (mret v') ∗
                                             ⌜ v = PairV (LitV $ LitInt (fst v'))
                                                         (LitV $ LitInt (snd v')) ⌝ }}%I.
Proof.
  iIntros "Hprob". rewrite /list_client.
  wp_bind (list_gen).
  iApply wp_wand_l; iSplitR ""; last first.
  { iApply list_gen_spec. }
  iIntros (v) "Hpost".
  iDestruct "Hpost" as (v1 v2 l1 l2) "Hpost". 
  iDestruct "Hpost" as %Hpure.
  destruct Hpure as (Hv&Hl1&Hl2&Hlen).
  wp_let.
  wp_bind (newcounter _).
  wp_apply (newcounter_spec' with "Hprob").
  iIntros (γl γp γv l) "Hcounter".
  rewrite -(Qp_div_2 1).
  assert (∃ k, lenTrue l1 + (lenTrue l2 + k) = max_length)%nat as (k&Heqk).
  { exists (max_length - lenTrue l1 - lenTrue l2)%nat. omega. }
  rewrite -{2}Heqk.
  rewrite Acounter_sep.
  iDestruct "Hcounter" as "(Hcounter1&Hcounter2)".
  rewrite Hv. 
  wp_let. wp_proj. wp_let.
  do 2 (wp_proj; wp_proj; wp_let).
   wp_apply (wp_par (λ v, Acounter max_length γl γp γv l (1 / 2)%Qp 0)%I
                    (λ v, Acounter  max_length γl γp γv l (1 / 2)%Qp k)%I
               with "[Hcounter1] [Hcounter2]").
  - rewrite -Hl1. wp_apply (countTrue_spec with "[Hcounter1]").
    { iFrame. iPureIntro; omega. }
    iIntros (_); auto.
    rewrite Nat.sub_diag; auto.
  - rewrite -Hl2. wp_apply (countTrue_spec with "[Hcounter2]").
    { iFrame. iPureIntro; omega. }
    iIntros (_); auto.
    replace (lenTrue l2 + k - lenTrue l2)%nat with k by omega.
    auto.
  - iIntros (v1' v2') "(Hpost1&Hpost2)".
    iCombine "Hpost1" "Hpost2" as "Hpost".
    rewrite Acounter_join Qp_div_2 //=.
    iNext. wp_let. wp_apply (read_spec' with "Hpost"); eauto.
    iIntros (v') "Hown". wp_value_head. 
    iExists ((max_length - k)%nat, v').
    iFrame. iPureIntro.
    rewrite -Heqk; f_equal. repeat f_equal.
    rewrite -Nat2Z.inj_add //=. f_equal.
    omega.
Qed.
End nondet_list_client.


End proof.


Section adequate.
Let Σ : gFunctors := #[ heapΣ ; spawnΣ; acounterΣ].

Definition client_ival sch e σ k := @ivdist_tpool_stepN heap_ectxi_lang sch [e] σ k.

Lemma generic_client_adequate n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0 0) -∗
   WP e {{ v, ∃ v' : nat * nat, ownProb (mret v') ∗ ⌜v = PairV #(fst v') #(snd v')⌝ }})%I →
  terminates sch [([e], σ)] k →
  irrel_couplingP (client_ival sch e σ k)
                  (approx_n n O O)
                  (prob_adequacy.coupling_post (λ x (y: nat * nat), x = PairV #(fst y) #(snd y))).
Proof.
  intros Hspec ?.
  eapply (heap_prob_adequacy Σ (approx_n n 0 0)
                             e σ (λ x y, x = PairV #(fst y) #(snd y)) sch k); eauto.
  intros. iIntros "Hprob".
  iApply Hspec; done.
Qed.

Lemma generic_client_ex_Ex_ival n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0 0) -∗
   WP e {{ v, ∃ v' : nat * nat, ownProb (mret v') ∗ ⌜v = PairV #(fst v') #(snd v')⌝ }})%I →
  terminates sch [([e], σ)] k →
  ex_Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (PairV (LitV (LitInt y))
                                          (LitV (LitInt y'))) => IZR y - IZR y'
                            | _ => 0
                            end
                end) (client_ival sch e σ k).
Proof.
    intros. eapply irrel_coupling_eq_ex_Ex_supp; last first.
    { apply pspec_bounded. eexists. apply approx_n_bounded_diff. }
    eapply irrel_coupling_conseq; last first.
    * eapply irrel_coupling_proper; last eapply generic_client_adequate.
      ** reflexivity.
      ** reflexivity. 
      ** eauto.
      ** eauto.
    * intros x y.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=.
      inversion 1 => //=.
      subst.
      rewrite ?INR_IZR_INZ. done.
Qed.

Lemma generic_client_Ex_ival n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0 0) -∗
   WP e {{ v, ∃ v' : nat * nat, ownProb (mret v') ∗ ⌜v = PairV #(fst v') #(snd v')⌝ }})%I →
  terminates sch [([e], σ)] k →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (PairV (LitV (LitInt y))
                                          (LitV (LitInt y'))) => IZR y - IZR y'
                            | _ => 0
                            end
                end) (client_ival sch e σ k)
  = 0.
Proof.
  intros. replace 0 with (INR 0 - INR 0) by nra.
  apply stochastic_order.Finite_inj.
  apply Rbar_le_antisym.
  - rewrite -(Ex_max_approx_n n).
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
      destruct v0 => //=.
      inversion 1 => //=.
      subst.
      rewrite ?INR_IZR_INZ. done.
    * apply pspec_bounded. eexists. apply approx_n_bounded_diff.
  - rewrite -(Ex_min_approx_n n).
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
      destruct v0 => //=.
      inversion 1 => //=.
      subst.
      rewrite ?INR_IZR_INZ. done.
    * apply pspec_bounded. eexists. apply approx_n_bounded_diff.
Qed.

Variable list_gen : expr.
Variable max_length : nat.

Lemma list_client_Ex_ival sch σ k:
  terminates sch [([list_client list_gen], σ)] k →
  (∀ `{heapG Σ} `{H: probG Σ},
  (WP list_gen
   {{ v, ∃ (v1 v2 : val) (l1 l2 : seq bool),
         ⌜v = (#(lenTrue l1 + lenTrue l2), (v1, v2))%V
         ∧ l2tuple l1 = v1 ∧ l2tuple l2 = v2 ∧ (lenTrue l1 + lenTrue l2 ≤ max_length)%nat⌝ }})%I) →
  Ex_ival (λ x, match fst x with
                | [] => 0
                | e :: _ => match prob_language.to_val e with
                            | Some (PairV (LitV (LitInt y))
                                          (LitV (LitInt y'))) => IZR y - IZR y'
                            | _ => 0
                            end
                end) (client_ival sch (list_client list_gen) σ k)
  = 0.
Proof.
  intros ? Hpre.
  eapply generic_client_Ex_ival; auto.
  iIntros; iApply (list_client_spec _ max_length); first eapply Hpre; eauto.
Qed.

End adequate.
End COUNTER.