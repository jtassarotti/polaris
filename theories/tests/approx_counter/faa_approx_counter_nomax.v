Require Import Reals Psatz Omega.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth.
From iris.heap_lang Require Import proofmode notation par.
From iris Require heap_lang.lib.counter.
From mathcomp Require Import seq fintype.
From Coquelicot Require AutoDerive.
Import Derive.

Section COUNTER.

Definition newcounter : val := λ: <>, ref #0.
Definition min : val :=
  λ: "x" "y", if: "x" < "y" then "x" else "y".
Definition incr : val := λ: "l",
    let: "n" := !"l" in
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
  
Definition approx_incr curr : pidist nat :=
  k ← select_upto curr;
  flip_incr k.

(*
Fixpoint approx_n (n: nat) (l: nat) : pidist nat :=
  match n with
  | O => mret l
  | S n' =>
    x ← approx_incr l;
    approx_n n' (l + x)
  end.
*)

Fixpoint approx_n (n: nat) (l: nat) : pidist nat :=
  match n with
  | O => mret l
  | S n' =>
    x ← approx_incr l;
    approx_n n' (l + x)
  end.

Import Rbar.

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

Lemma approx_incr_bounded curr:
  pspec (approx_incr curr) (λ x : nat, Rabs (INR x) <= INR (S curr)).
Proof.
  eapply (pspec_mbind _ _ (λ x, x <= curr)%nat); first eapply select_upto_spec1.
  intros a Hle. rewrite /flip_incr.
  apply pspec_pidist_plus.
  * apply pspec_mret. rewrite Rabs_right.
    ** apply le_INR. omega.
    ** apply Rle_ge, pos_INR.
  * apply pspec_mret. rewrite S_INR //= Rabs_R0.
    specialize (pos_INR curr); nra.
Qed.

Fixpoint approx_n_bound n curr :=
  match n with
  | O => curr
  | S n' =>
    approx_n_bound n' (curr + S curr)%nat
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

Lemma Ex_min_approx_incr curr:
  Ex_min INR (approx_incr curr) = Finite 1.
Proof.
  rewrite /approx_incr.
  apply Ex_min_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S curr)).
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
  - transitivity (Ex_min (λ x : nat, INR (n + l) + INR x) (approx_incr l)).
    { rewrite Ex_min_bind_post -/approx_n.
      * apply Ex_min_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
        nra.
      * apply Ex_min_bounded_supp_fun_finite.
        apply pspec_bounded. 
        eexists (INR (n + l + l + 1)). eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn. rewrite ?Rabs_right in Hle *; try apply Rle_ge, pos_INR.
        apply le_INR. apply INR_le in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (approx_n_bound (S n) l)).
        eapply (approx_n_bounded (S n) l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (n + l + (l  + 1))).
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

Lemma Ex_max_approx_incr curr:
  Ex_max INR (approx_incr curr) = 1.
Proof.
  rewrite /approx_incr.
  apply Ex_max_bind_const.
  { apply ex_Ex_extrema_bounded_supp_fun.
    eapply pspec_bounded. exists (INR (S curr)).
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
  - transitivity (Ex_max (λ x : nat, INR (n + l) + INR x) (approx_incr l)).
    { rewrite Ex_max_bind_post -/approx_n.
      * apply Ex_max_eq_ext.
        intros n'. rewrite IHn.
        rewrite ?plus_INR //=.
        nra.
      * apply Ex_max_bounded_supp_fun_finite.
        apply pspec_bounded. 
        eexists (INR (n + l + l + 1)). eapply pspec_conseq; first eapply approx_incr_bounded.
        intros a Hle.
        rewrite IHn. rewrite ?Rabs_right in Hle *; try apply Rle_ge, pos_INR.
        apply le_INR. apply INR_le in Hle. omega.
      * intros. rewrite IHn => //=.
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (approx_n_bound (S n) l)).
        eapply (approx_n_bounded (S n) l).
      * apply ex_Ex_extrema_bounded_supp_fun.
        eapply pspec_bounded. exists (INR (n + l + (l  + 1))).
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

Fixpoint Ex_max2_bound (n: nat) (l: nat) : R :=
  match n with
  | O => (INR l)^2
  | S n' => 1/(INR l + 1) * Ex_max2_bound n' (l + l + 1) +
            (INR l) / (INR l + 1) * Ex_max2_bound n' l
  end.

Lemma Ex_max2_bound_closed n l:
  Ex_max2_bound n l = -1/2 * INR n + 3/2 * (INR n)^2 + 3 * INR n * INR l + (INR l)^2.
Proof.
  revert l.
  induction n => l.
  - replace (INR 0) with 0 by auto. ring_simplify. rewrite //=.
  - simpl Ex_max2_bound. rewrite ?IHn. rewrite ?S_INR ?plus_INR. replace (INR 1) with 1 by auto.
    field. specialize (pos_INR l). nra.
Qed.

Definition Ex_max2_gen n l :=
  -1/2 * INR n + 3/2 * (INR n)^2 + 3 * INR n * l + l^2.

Lemma Ex_max2_bound_to_gen n l :
  Ex_max2_bound n l = Ex_max2_gen n (INR l).
Proof. rewrite Ex_max2_bound_closed //=. Qed.

Lemma Ex_max2_gen_skew n l k1 k2:
  0 <= k1 <= k2 →
  1/(k1 + 1) * Ex_max2_gen n (l + k1 + 1) +
  k1/(k1 + 1) * Ex_max2_gen n l <=
  1/(k2 + 1) * Ex_max2_gen n (l + k2 + 1) +
  k2/(k2 + 1) * Ex_max2_gen n l.
Proof.
  intros Hrange.
  destruct Hrange as (Hrange1&Hrange2).
  inversion Hrange2; last first.
  { subst. rewrite //=. }
  left.
  eapply (incr_function_le) with (f := (λ x, 1 / (x + 1) * Ex_max2_gen n (l + x + 1)
                                             + x / (x + 1) * Ex_max2_gen n l))
                                 (a := 0)
                                 (b := k2); auto.
  { rewrite //=.
    intros. rewrite /Ex_max2_gen.
    match goal with
    | |- is_derive ?f ?v ?l =>
      AutoDerive.auto_derive_fun f
    end.
    rewrite //=. intros Heq. eapply Heq. split; nra.
  }
  { 
    rewrite //=; intros. field_simplify; try nra.
    apply Rlt_gt. replace (0 / 1) with 0 by field.
    apply Rdiv_lt_0_compat; nra.
  }
  reflexivity.
Qed.

Lemma Ex_max2_skew n l k1 k2:
  (k1 <= k2)%nat →
  1/(INR k1 + 1) * Ex_max2_bound n (l + k1 + 1) +
  (INR k1)/(INR k1 + 1) * Ex_max2_bound n l <=
  1/(INR k2 + 1) * Ex_max2_bound n (l + k2 + 1) +
  (INR k2)/(INR k2 + 1) * Ex_max2_bound n l.
Proof.
  rewrite ?Ex_max2_bound_to_gen.
  rewrite ?plus_INR. replace (INR 1) with 1 by auto.
  intros Hle. apply Ex_max2_gen_skew; split; auto using pos_INR, le_INR.
Qed.

Lemma approx_n_bounded2 n l:
  bounded_fun_on (λ x : nat, INR x ^ 2) (λ x : nat, In_psupport x (approx_n n l)).
Proof.
  exists (INR (approx_n_bound n l)^2).
  eapply pspec_conseq; first eapply approx_n_bounded.
  intros x => //=.
  rewrite ?Rabs_right ?Rmult_1_r -?mult_INR; auto using Rle_ge, pos_INR.
  intros ?%INR_le. apply le_INR, mult_le_compat; auto.
Qed.

Lemma Ex_max2_approx_n_finite (n: nat) l:
  is_finite (Ex_max (λ x, (INR x)^2) (approx_n n l)).
Proof.
  apply Ex_max_bounded_supp_fun_finite, approx_n_bounded2.
Qed.

Lemma Ex_max2_approx_n_ex n l:
  ex_Ex_extrema (λ x : nat, INR x ^ 2) (approx_n n l).
Proof.
  apply ex_Ex_extrema_bounded_supp_fun, approx_n_bounded2.
Qed.

Lemma Rbar_le_finite x y: x <= y → Rbar_le (Finite x) (Finite y).
Proof.  auto. Qed.

Import Lub.

Lemma Ex_max2_approx_n (n: nat) l:
  Rbar_le (Ex_max (λ x, (INR x)^2) (approx_n n l))
          (Finite (Ex_max2_bound n l)).
Proof.
  assert (∀ l (choice : pidist nat),
             (List.In choice (mret 0%nat :: [seq mret i | i <- iota 1 l])) →
             ∃ k, choice = mret k ∧ 0 <= k <= l)%nat as Hchoice_inv.
  { clear. intros l choice Hchoice. destruct Hchoice as [Hc1|Hc2]; subst.
    * eexists; split; eauto; omega.
    *  apply in_map_iff in Hc2 as (k&?&?). exists k; split; auto.
       apply Iter.In_iota; auto. right. auto.
  }

  revert l. induction n => l.
  - rewrite Ex_max_mret //=.
  - simpl approx_n. rewrite /approx_incr pidist_assoc.
    rewrite /select_upto.
    rewrite pidist_union_fold_left_join pidist_join_bind.
    rewrite Ex_max_pidist_join.
    * apply Lub_Rbar_correct.
      intros r ((choice&Hchoice)&Heq).
      destruct (Hchoice_inv _ _ Hchoice) as (k&Hkeq&Hkrange).
      rewrite -Heq. simpl proj1_sig. rewrite Hkeq.
      setoid_rewrite pidist_left_id.
      rewrite /flip_incr.
      rewrite Ex_max_pidist_plus_bind.
      ** setoid_rewrite (pidist_left_id (S k)).
         setoid_rewrite (pidist_left_id O).
         simpl Ex_max2_bound.
         etransitivity; last first.
         {
           apply Rbar_le_finite.
           eapply (Ex_max2_skew _ l k).
           omega.
         }
         apply Rplus_le_compat.
         *** apply Rmult_le_compat_l.
             {  apply Rcomplements.Rdiv_le_0_compat; specialize (pos_INR k); nra. }
             specialize (IHn (l + S k)%nat).
             rewrite -Ex_max2_approx_n_finite //= in IHn *.
             replace (l + k + 1)%nat with (l + S k)%nat by omega. auto.
         *** assert (1 - 1 / (INR k + 1) = INR k / (INR k + 1)) as ->.
             { field. specialize (pos_INR k). nra. }
             apply Rmult_le_compat_l.
             {  apply Rcomplements.Rdiv_le_0_compat; specialize (pos_INR k); nra. }
             specialize (IHn l)%nat.
             rewrite -Ex_max2_approx_n_finite //= in IHn *.
             replace (l + 0)%nat with l by omega; auto.
      ** setoid_rewrite pidist_left_id. apply Ex_max2_approx_n_finite.
      ** setoid_rewrite pidist_left_id. apply Ex_max2_approx_n_finite.
      ** setoid_rewrite pidist_plus_bind.
         apply ex_Ex_extrema_pidist_plus; setoid_rewrite pidist_left_id;
           apply Ex_max2_approx_n_ex.
    * intros (?&Hin). simpl proj1_sig.
      edestruct (Hchoice_inv _ _ Hin) as (k&Heq&Hin').
      rewrite Heq. setoid_rewrite pidist_left_id.
      setoid_rewrite pidist_plus_bind; setoid_rewrite pidist_left_id.
      apply Ex_max_bounded_supp_fun_finite, bounded_psupp_pidist_plus;
        apply approx_n_bounded2.
Qed.
  
Global Instance Rbar_plus_le_Proper:
  Proper (Rbar_le ==> Rbar_le ==> Rbar_le) Rbar_plus.
Proof. intros ?? ? ?? ?. apply Rbar_plus_le_compat; eauto. Qed.

From discprob.idxval Require Import markov.
Lemma approx_n_chebyshev n k:
  k > 0 →
  Rbar_le (Pr_max (λ x, Rabs (INR x - INR n) > k) (approx_n n O))
          ((/k^2) * (((INR n)^2 - INR n)/2)).
Proof.
  intros Hgt. etransitivity; first eapply chebyshev_inequality; auto.
  { apply Ex_max_bounded_supp_fun_finite.
    apply bounded_psupp_variance_moment2, approx_n_bounded2. }
  { apply ex_Ex_extrema_bounded_supp_fun.
    apply bounded_psupp_variance_moment2, approx_n_bounded2. }
  etransitivity.
  { apply Rbar_mult_finite_le_compat_l.
    { left. apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; auto. nra. }
    apply Ex_max_variance; last apply Rle_ge, pos_INR.
    apply Ex_max2_approx_n_ex.
  }
  rewrite [a in Rbar_le _ a]Finite_Rmult.
  apply (Rbar_mult_finite_le_compat_l (/ k ^ 2)).
  { left. apply Rinv_0_lt_compat.
    apply Rmult_lt_0_compat; auto. nra.
  }
  setoid_rewrite Ex_max2_approx_n.
  rewrite Ex_min_approx_n Ex_max2_bound_closed plus_INR //=.
  field_simplify.
  done.
Qed.

Class acounterG Σ :=
  ACounterG { acounter1_inG :> inG Σ (frac_authR natR) }. 
Definition acounterΣ : gFunctors := #[GFunctor (frac_authR natR); GFunctor (authR mnatUR)].
Instance subG_acounterΣ {Σ} : subG acounterΣ Σ → acounterG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{!heapG Σ, !probG Σ, !acounterG Σ, !spawnG Σ, !heap_lang.lib.counter.mcounterG Σ}.


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

(*
Definition acounter_loc_inv (γl : gname) (l : loc) : iProp Σ :=
  (∃ n, own γl (◯!{1/2} n) ∗ l ↦ #n)%I.
*)

Definition acounter_prob_inv (γp γv γv' γg γl: gname) (l : loc): iProp Σ :=
  (∃ n1 n2 n3 gap, ⌜ (n3 + gap = n2)%nat ⌝
                 ∗ own γp (●! n1)
                 ∗ own γv (●! n2) ∗ own γv' (● (n2 : mnat))
                 ∗ own γl (●! n3)
                 ∗ own γg (●! gap)
                 ∗ l ↦ #n3
                 ∗ (own γp (◯! n1) ∨ ownProb (approx_n n1 n2)))%I.

Definition acounter (γl γp γv γg: gname) (q : frac) (nperm : nat) (ncontrib : nat) : iProp Σ :=
  (own γp (◯!{q} nperm) ∗ own γl (◯!{q} ncontrib) ∗ own γv (◯!{q} ncontrib)
    ∗ own γg (◯!{q} O))%I.

Lemma acounter_sep γl γp γv γg q1 q2 np1 np2 nc1 nc2 :
  acounter γl γp γv γg (q1 + q2) (np1 + np2) (nc1 + nc2) ⊢
           acounter γl γp γv γg q1 np1 nc1 ∗ acounter γl γp γv γg q2 np2 nc2.
Proof.
  rewrite /acounter.
  iStartProof. 
  * iIntros "(Hown1&Hown2&Hown3&Hown4)".  
    rewrite ?frag_auth_op -?own_op.
    iDestruct "Hown1" as "(?&?)". 
    iDestruct "Hown2" as "(?&?)". 
    iDestruct "Hown3" as "(?&?)". 
    iDestruct "Hown4" as "(?&?)". 
    iFrame.
Qed.

Lemma acounter_join γl γp γv γg q1 q2 np1 np2 nc1 nc2 :
  acounter γl γp γv γg q1 np1 nc1 ∗ acounter γl γp γv γg q2 np2 nc2 ⊢
           acounter γl γp γv γg (q1 + q2) (np1 + np2) (nc1 + nc2).
Proof.
  rewrite /acounter.
  iStartProof. 
  * iIntros "((Hown1a&Hown2a&Hown3a&Hown4a)&(Hown1b&Hown2b&Hown3b&Hown4b))".  
    iCombine "Hown1a" "Hown1b" as "Hown1".
    iCombine "Hown2a" "Hown2b" as "Hown2".
    iCombine "Hown3a" "Hown3b" as "Hown3".
    iCombine "Hown4a" "Hown4b" as "Hown4".
    iFrame.
Qed.

Lemma incr_spec N γl γp γv γv' γg l q np nc:
  {{{ inv N (acounter_prob_inv γp γv γv' γg γl l) ∗
      acounter γl γp γv γg q (S np) nc }}}
    incr (Lit $ LitLoc l) 
  {{{ RET LitV LitUnit; ∃ nc' : nat, acounter γl γp γv γg q np nc' }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(#Hinv&(Hγp&Hγl&Hγv&Hγg))".
  rewrite /incr.
  wp_let. wp_bind (! _)%E.
  iInv N as (np_global nv_global nl_global gap)
              ">(%&Hγp'&Hγv'&Hγv''&Hγl'&Hγg'&Hl&Hprob)" "Hclose".
  iMod (own_update with "Hγv''") as "[Hγv'' Hrem]".
  { apply auth_update_alloc, (mnat_local_update _ _ nv_global); auto. }
  wp_load.
  iMod ("Hclose" with "[Hγp' Hγv' Hγv'' Hγl' Hγg' Hl Hprob]") as "_".
  { iNext; iExists np_global, nv_global, nl_global, gap; by iFrame. } 

  iModIntro.
  wp_let. 

  wp_op.
  wp_bind (flip _ _).
  iInv N as (np_global' nv_global' nl_global'
              gap') ">(%&Hγp'&Hγv'&Hγv''&Hγl'&Hγg'&Hl&Hprob)" "Hclose".
  iDestruct "Hprob" as "[Hbad|Hprob]".
  { iDestruct (own_valid_2 with "Hbad Hγp") as %?%frac_auth_frag_valid_op_1_l; done. }

  iDestruct (own_valid_2 with "Hγp' Hγp") as % ?%frac_auth_included_total%nat_included.
  destruct np_global' as [|np_global']; first by omega.
  rewrite /approx_n -/approx_n.

  iAssert (⌜ nl_global ≤ nv_global' ⌝)%I with "[Hrem Hγv'']" as "%".
  {  
    iDestruct (own_valid_2 with "Hγv'' Hrem")
      as %[?%mnat_included _]%auth_valid_discrete_2.
    iPureIntro; omega.
  }

  assert (0 <= IZR 1 / IZR (nl_global + 1) ∧ IZR 1 / IZR (nl_global + 1) <= 1).
  {
    rewrite //=.
    replace (IZR (nl_global + 1)) with (INR nl_global + 1).
    * apply INRp1_prob.
    * rewrite plus_IZR; f_equal.
      rewrite INR_IZR_INZ. done.
  }

  unshelve (wp_flip (approx_incr nv_global')
                    (λ x y, if (x : bool) then (Z.of_nat y) = (nl_global + 1)%Z
                            else Z.of_nat y = O) b z' HR); auto.
    { rewrite /approx_incr/select_upto. eapply irrel_coupling_proper.
      { reflexivity.  }
      { setoid_rewrite pidist_union_foldleft_bind. reflexivity. }
      apply ip_irrel_coupling.
      eapply (ip_coupling_union_list _ (flip_incr (Z.to_nat nl_global))).
      - rewrite /flip_incr.
        apply ip_coupling_plus.
        { rewrite //=.  f_equal. rewrite plus_IZR. f_equal.
          rewrite INR_IZR_INZ. f_equal.
          rewrite Z2Nat.id; auto.
          omega.
        }
        * apply ip_coupling_mret.
          rewrite -Z2Nat.inj_succ; last omega.
          rewrite Z2Nat.id; auto.
          cut (0 ≤ nl_global); try omega.
        * apply ip_coupling_mret.
          split; auto => //=.
      - eexists. split; last first.
        { rewrite -List.map_cons. 
          eapply in_map_iff.
          exists (mret (Z.to_nat nl_global)); split.
          * reflexivity.
          * rewrite -map_cons. eapply in_map_iff.
            exists (Z.to_nat nl_global); split; auto.
            replace (O :: iota 1 nv_global') with (iota O (S nv_global' - 0)); last first.
            { rewrite //=.  }
            apply Iter.In_iota; split.
            **  omega. 
            ** rewrite //=. rewrite Nat2Z.id. omega.
        }
        setoid_rewrite pidist_left_id. reflexivity.
    }
    rewrite //= in HR. (* destruct HR as (Heqz&?); subst. *)
    destruct b.
    * iMod (own_update_2 with "Hγp' Hγp") as "[Hγp' Hγp]".
      { apply frac_auth_update, (nat_local_update _ _ (np_global') (np)). omega. }
      iMod (own_update_2 with "Hγv' Hγv") as "[Hγv' Hγv]".
      { apply frac_auth_update, (nat_local_update _ _ (nv_global' + z') (nc + z')); omega. }
      iMod (own_update with "Hγv''") as "[Hγ'' Hrem'']".
      {  apply auth_update_alloc, (mnat_local_update _ _ (nv_global' + z')%nat); omega. } 
      iMod (own_update_2 with "Hγg' Hγg") as "[Hγg' Hγg]".
      {  apply frac_auth_update, (nat_local_update _ _ (gap' + z')%nat (0 + z')%nat); omega. } 
      iMod ("Hclose" with "[Hγp' Hγv' Hγ'' Hγl' Hγg' Hl Hprob]").
      { iNext. iExists np_global', (nv_global' + z')%nat, nl_global', (gap' + z')%nat. iFrame.
        iSplitL ""; first (iPureIntro; omega). 
        iRight. iFrame. }

      iModIntro.
      wp_let.
      wp_if.
      wp_op.
      wp_bind (FAA _ _).
      iInv N as (np_global'' nv_global'' nl_global'' gap'')
                  ">(%&Hγp'&Hγv'&Hγv''&Hγl'&Hγg'&Hl&Hprob)" "Hclose".

      wp_faa.
      iDestruct (own_valid_2 with "Hγg' Hγg") as % ?%frac_auth_included_total%nat_included.

      iMod (own_update_2 with "Hγl' Hγl") as "[Hγl' Hγl]".
      { apply frac_auth_update, (nat_local_update _ _ (nl_global'' + z') (nc + z')); omega. }

      iMod (own_update_2 with "Hγg' Hγg") as "[Hγg' Hγg]".
      { apply frac_auth_update, (nat_local_update _ _ (gap'' - z') 0). omega. }


      iMod ("Hclose" with "[Hγp' Hγv' Hγv'' Hγl' Hγg' Hl Hprob]").
      { iNext. iExists np_global'', nv_global'', (nl_global'' + z')%nat, (gap'' - z')%nat. iFrame.
        rewrite ?Nat2Z.inj_add => //=.
        rewrite HR. rewrite Zplus_comm. iFrame. iPureIntro. omega.
      }

      iModIntro. wp_let.
      iApply "HΦ".
      iExists (nc + z')%nat.
      iFrame.
    * replace (nv_global + z')%nat with (nv_global); last first.
      { apply Z_of_nat_inj. rewrite Nat2Z.inj_add HR. omega. }
      iMod (own_update_2 with "Hγp' Hγp") as "[Hγp' Hγp]".
      { apply frac_auth_update, (nat_local_update _ _ (np_global') (np)); omega. }
      iMod ("Hclose" with "[Hγp' Hγv' Hγv'' Hγg' Hγl' Hl Hprob]").
      { iNext. iExists np_global', nv_global', nl_global', gap'. iFrame.
        iSplitL ""; first by (iPureIntro; omega).
        iRight. assert (z' = 0)%nat by omega. subst.
        replace (nl_global' + gap' + 0)%nat with (nl_global' + gap')%nat by omega.
        iFrame.
      }
      iModIntro.
      wp_let.
      wp_if.

      iApply "HΦ".
      iExists nc. iFrame.
Qed.

Lemma read_spec N γl γp γv γv' γg l nc:
  {{{inv N (acounter_prob_inv γp γv γv' γg γl l) ∗
      acounter γl γp γv γg 1 0 nc }}}
    read (Lit $ LitLoc l) 
  {{{ (v : nat), RET LitV $ LitInt v; ownProb (mret v) }}}. 
Proof.
  iIntros (ϕ) "Hpre HΦ".
  iDestruct "Hpre" as "(#Hinv&(Hγp&Hγl&Hγv&Hγg))".
  wp_let. 
  iInv N as (np_global nv_global nl_global gap) ">(%&Hγp'&Hγv'&Hγv''&Hγl'&Hγg'&Hl&Hprob)" "Hclose2".
  iDestruct "Hprob" as "[Hbad|Hprob]".
  { iDestruct (own_valid_2 with "Hbad Hγp") as %?%frac_auth_frag_valid_op_1_l; done. }
  wp_load.
  iDestruct (own_valid_2 with "Hγp' Hγp") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγl' Hγl") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγv' Hγv") as % ->%frac_auth_agreeL.
  iDestruct (own_valid_2 with "Hγg' Hγg") as % ->%frac_auth_agreeL.
  iMod ("Hclose2" with "[Hγp' Hγv' Hγp Hγl' Hγv'' Hγg' Hl]").
  { iNext. iExists O, nc, nc, O. iFrame.
    iSplitL ""; first by (iPureIntro; omega).
    iLeft. iFrame. }

  iModIntro. iApply "HΦ". rewrite //=.
Qed.

Lemma newcounter_spec N n :
  {{{ ownProb (approx_n n O)}}}
    newcounter #()
  {{{ γl γp γv γv' γg l, RET #l;
      inv N (acounter_prob_inv γp γv γv' γg γl l) ∗
     acounter γl γp γv γg 1 n O }}}.
Proof.
  iIntros (Φ) "Hprob HΦ".
  iMod (own_alloc (●! O%nat ⋅ ◯! O%nat)) as (γl) "[Hγl' Hγl]"; first done.
  iMod (own_alloc (●! n%nat ⋅ ◯! n%nat)) as (γp) "[Hγp' Hγp]"; first done.
  iMod (own_alloc (●! O%nat ⋅ ◯! O%nat)) as (γv) "[Hγv' Hγv]"; first done.
  iMod (own_alloc (●! O%nat ⋅ ◯! O%nat)) as (γg) "[Hγg' Hγg]"; first done.
  iMod (own_alloc (● (O: mnat) ⋅ ◯ (O: mnat))) as (γv') "[Hγv'' _]"; first done.

  rewrite -wp_fupd /newcounter /=.
  wp_let. wp_alloc l as "Hl".
  iMod (inv_alloc N _ (acounter_prob_inv γp γv γv' γg γl l) with
            "[Hγp' Hγv' Hγv'' Hprob Hγg' Hγl' Hl]").
  { iNext. iExists n, O, O, O. iFrame.
    iSplitL ""; first by (iPureIntro; omega).
    iRight. done. }

  iApply "HΦ".
  iModIntro. iFrame.
Qed.
End proof.

Section adequate.
Let Σ : gFunctors := #[ heapΣ ; spawnΣ; acounterΣ; heap_lang.lib.counter.mcounterΣ].

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

Definition ICR (x: cfg heap_lang) : R :=
  match fst x with
  | [] => 0
  | e :: _ => match prob_language.to_val e with
              | Some (LitV (LitInt y)) => IZR y
              | _ => 0
              end
  end.

Lemma generic_client_Ex_ival n sch e σ k:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0) -∗
   WP e {{ v, ∃ v' : nat, ownProb (mret v') ∗ ⌜v = #v'⌝ }})%I →
  terminates sch [([e], σ)] k →
  Ex_ival ICR (client_ival sch e σ k)
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
    * intros x y. rewrite /ICR.
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
    * intros x y. rewrite /ICR.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=. destruct l0 => //=.
      inversion 1. subst.
      rewrite INR_IZR_INZ. done.
    * apply pspec_bounded. eexists. apply approx_n_bounded.
Qed.

Lemma generic_client_chebyshev n sch e σ k δ:
  (∀ `{heapG Σ} `{H: probG Σ},
    ownProb (approx_n n 0) -∗
   WP e {{ v, ∃ v' : nat, ownProb (mret v') ∗ ⌜v = #v'⌝ }})%I →
  terminates sch [([e], σ)] k →
  δ > 0 →
  Pr (λ x, Rabs (ICR x - INR n) > δ) (client_ival sch e σ k)
  <= ((/δ^2) * (((INR n)^2 - INR n)/2)).
Proof.
  intros.
  cut 
  (Finite (Pr (λ x, Rabs (ICR x - INR n) > δ) (client_ival sch e σ k))
   <= ((/δ^2) * (((INR n)^2 - INR n)/2))).
  { auto. }
  apply Series_Ext.Rbar_le_fin.
  { specialize (pos_INR n). intros.
    apply Rmult_le_pos.
    * left. apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; nra.
    * cut (INR n <= INR n^2); first nra.
      rewrite //= Rmult_1_r -mult_INR.
      apply le_INR. clear.
      induction n; auto.
      transitivity (n * n + 1)%nat; first omega.
      ring_simplify.
      omega.
  }
  etransitivity; last apply approx_n_chebyshev; auto.
  intros. apply irrel_coupling_eq_Ex_max_supp.
    eapply irrel_coupling_conseq; last first.
    * eapply irrel_coupling_proper; last eapply generic_client_adequate.
      ** reflexivity.
      ** reflexivity. 
      ** eauto.
      ** eauto.
    * intros x y. rewrite /ICR.
      destruct x as ([| v ?]&?) => //=.
      destruct (to_val v) => //=.
      destruct v0 => //=. destruct l0 => //=.
      inversion 1. subst.
      rewrite ?INR_IZR_INZ. done.
    * apply pspec_bounded. exists 1 => ??.
      destruct (ClassicalEpsilon.excluded_middle_informative) => //=; rewrite Rabs_right; nra.
Qed.

End adequate.
End COUNTER.