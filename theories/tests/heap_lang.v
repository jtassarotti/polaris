(** This file is essentially a bunch of testcases. *)
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import adequacy.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Section LiftingTests.
  Context `{heapG Σ} `{probG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition simpl_test :
    ⌜(10 = 4 + 6)%nat⌝ -∗
    WP let: "x" := ref #1 in "x" <- !"x";; !"x" {{ v, ⌜v = #1⌝ }}.
  Proof.
    iIntros "?". wp_alloc l. repeat (wp_pure _) || wp_load || wp_store.
    match goal with
    | |- context [ (10 = 4 + 6)%nat ] => done
    end.
  Qed.

  Definition heap_e : expr :=
    let: "x" := ref #1 in "x" <- !"x" + #1 ;; !"x".

  Lemma heap_e_spec E : WP heap_e @ E {{ v, ⌜v = #2⌝ }}%I.
  Proof.
    iIntros "". rewrite /heap_e.
    wp_alloc l. wp_let. wp_load. wp_op. wp_store. by wp_load.
  Qed.

  Definition heap_e2 : expr :=
    let: "x" := ref #1 in
    let: "y" := ref #1 in
    "x" <- !"x" + #1 ;; !"x".

  Lemma heap_e2_spec E : WP heap_e2 @ E {{ v, ⌜v = #2⌝ }}%I.
  Proof.
    iIntros "". rewrite /heap_e2.
    wp_alloc l. wp_let. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_store. wp_load. done.
  Qed.

  Definition heap_e3 : expr :=
    let: "x" := #true in
    let: "f" := λ: "z", "z" + #1 in
    if: "x" then "f" #0 else "f" #1.

  Lemma heap_e3_spec E : WP heap_e3 @ E {{ v, ⌜v = #1⌝ }}%I.
  Proof.
    iIntros "". rewrite /heap_e3.
    by repeat (wp_pure _).
  Qed.

  Definition heap_e4 : expr :=
    let: "x" := (let: "y" := ref (ref #1) in ref "y") in
    ! ! !"x".

  Lemma heap_e4_spec : WP heap_e4 {{ v, ⌜ v = #1 ⌝ }}%I.
  Proof.
    rewrite /heap_e4. wp_alloc l. wp_alloc l'. wp_let.
    wp_alloc l''. wp_let. by repeat wp_load.
  Qed.

  Definition heap_e5 : expr :=
    let: "x" := ref (ref #1) in FAA (!"x") (#10 + #1) + ! !"x".

  Lemma heap_e5_spec E : WP heap_e5 @ E {{ v, ⌜v = #13⌝ }}%I.
  Proof.
    rewrite /heap_e5. wp_alloc l. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_faa. do 2 wp_load. wp_op. done.
  Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + #1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ #0 then -FindPred (-"x" + #2) #0 else FindPred "x" #0.

  Lemma FindPred_spec n1 n2 E Φ :
    n1 < n2 →
    Φ #(n2 - 1) -∗ WP FindPred #n2 #n1 @ E {{ Φ }}.
  Proof.
    iIntros (Hn) "HΦ". iLöb as "IH" forall (n1 Hn).
    wp_rec. wp_let. wp_op. wp_let.
    wp_op; case_bool_decide; wp_if.
    - iApply ("IH" with "[%] HΦ"). omega.
    - by assert (n1 = n2 - 1) as -> by omega.
  Qed.

  Lemma Pred_spec n E Φ : ▷ Φ #(n - 1) -∗ WP Pred #n @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". wp_lam.
    wp_op. case_bool_decide; wp_if.
    - wp_op. wp_op.
      wp_apply FindPred_spec; first omega.
      wp_op. by replace (n - 1) with (- (-n + 2 - 1)) by omega.
    - wp_apply FindPred_spec; eauto with omega.
  Qed.

  Lemma Pred_user E :
    (WP let: "x" := Pred #42 in Pred "x" @ E {{ v, ⌜v = #40⌝ }})%I.
  Proof. iIntros "". wp_apply Pred_spec. wp_let. by wp_apply Pred_spec. Qed.
End LiftingTests.

Lemma heap_e_adequate σ : adequate NotStuck heap_e σ (= #2).
Proof. eapply (heap_adequacy' heapΣ _)=> ??. by eapply heap_e_spec. Qed.
