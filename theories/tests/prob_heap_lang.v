(** This file is essentially a bunch of testcases. *)
Require Import Reals Psatz.
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import adequacy.
From iris.heap_lang Require Import proofmode notation.
From discprob.basic Require Import monad.
From discprob.idxval Require Import pival
     pival_dist ival_dist irrel_equiv idist_pidist_pair extrema.
Set Default Proof Using "Type".

Module tests.
Section tests.
  Context `{heapG Σ} `{probG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition heap_e2 : expr :=
    let: "x" := flip #1 #2 in
    let: "y" := flip #1 #2 in
    "x" = "y".

  Program Definition flip_half := pidist_plus (1/2)%R _ (mret true) (mret false).
  Next Obligation.
    nra.
  Qed.

  Lemma heap_e2_spec E :
    ownProb (flip_half) ⊢
            WP heap_e2 @ E {{ v, ∃ v', ownProb (mret v') ∗
                           ⌜ v = LitV $ LitBool v' ⌝ }}%I.
  Proof.
    iIntros "Hprob". rewrite /heap_e2.
    rewrite /flip_half.
    setoid_rewrite <-(pidist_left_id tt (λ x, flip_half)).
    unshelve (wp_flip (mret tt) (λ x y, True) b b' HR); first by abstract (nra).
    { apply irrel_coupling_trivial. }
    wp_let.
    setoid_rewrite <-(pidist_right_id) at 1.
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
        eapply (ip_coupling_proper (ivdplus _ H0 (mret false) (mret true))).
        { symmetry. eapply ivdplus_comm. } 
        { reflexivity.  }
        assert (1 - (IZR 1 / IZR 2) = IZR 1 / IZR 2)%R as Heq.
        { nra.  }
        generalize H0.
        rewrite Heq => ?.
        eapply ip_coupling_plus; first (by reflexivity);
          apply ip_coupling_mret; auto.
    }
    wp_let.
    subst.
    wp_op.
    iExists c'.
    iFrame.
    iPureIntro.
    destruct b, c; subst => //=.
  Qed.
End tests.


Section ClosedProofs.

  Let Σ : gFunctors := #[ heapΣ ].

  Variable (sch : @scheduler heap_ectxi_lang).
  Variable (σ : state).
  Variable (n : nat).

  Definition heap_e2_ival := ivdist_tpool_stepN sch [heap_e2] σ n.


  Lemma test_adequate_1 (Hterm: terminates sch [([heap_e2], σ)] n):
    irrel_couplingP (heap_e2_ival)
                    flip_half
                    (prob_adequacy.coupling_post (λ x y, x = LitV $ LitBool y)).
  Proof.
    intros.
    eapply (heap_prob_adequacy Σ flip_half
                              (heap_e2) σ (λ x y, x = LitV $ LitBool y) sch n); eauto.
    intros. iIntros "Hown". iPoseProof (heap_e2_spec with "Hown") as "H"; auto.
  Qed.

  Local Open Scope R.
  Import Rbar.

  Lemma test_Ex_min_false (Hterm: terminates sch [([heap_e2], σ)] n):
    Rbar_le (Ex_min (λ x : bool, if x then 0 else 1) flip_half)
            (Ex_ival (λ x,
                      match fst x with
                      | [] => 0
                      | e :: _ => match prob_language.to_val e with
                                  | Some (LitV (LitBool false)) => 1
                                  | _ => 0
                                  end
                      end) heap_e2_ival).
  Proof.
    apply irrel_coupling_eq_Ex_min; last first.
    { exists 1. intros []; rewrite Rabs_right; nra. }
    eapply irrel_coupling_conseq; last first.
    { eapply irrel_coupling_proper; last eapply test_adequate_1.
      - reflexivity.
      - reflexivity. 
      - eauto.
    }
    intros x b.
    destruct x as ([| v ?]&?) => //=.
    destruct (to_val v) => //=.
    destruct v0 => //=. destruct l0 => //=.
    destruct b0, b => //=.
  Qed.
    
  Lemma test_Ex_min_true (Hterm: terminates sch [([heap_e2], σ)] n):
    Rbar_le (Ex_min (λ x : bool, if x then 1 else 0) flip_half)
            (Ex_ival (λ x,
                      match fst x with
                      | [] => 0
                      | e :: _ => match prob_language.to_val e with
                                  | Some (LitV (LitBool true)) => 1
                                  | _ => 0
                                  end
                      end) heap_e2_ival).
  Proof.
    apply irrel_coupling_eq_Ex_min; last first.
    { exists 1. intros []; rewrite Rabs_right; nra. }
    eapply irrel_coupling_conseq; last first.
    { eapply irrel_coupling_proper; last eapply test_adequate_1.
      - reflexivity.
      - reflexivity. 
      - auto. 
    }
    intros x b.
    destruct x as ([| v ?]&?) => //=.
    destruct (to_val v) => //=.
    destruct v0 => //=. destruct l0 => //=.
    destruct b0, b => //=.
  Qed.

  Print Assumptions test_Ex_min_true.
End ClosedProofs.

End tests.
