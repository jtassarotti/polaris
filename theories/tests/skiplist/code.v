Require Import Reals Psatz Omega.
From Coq Require Export Sorted.
From iris.program_logic Require Export weakestpre prob_adequacy.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Export lang adequacy.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac_auth auth gset.
From iris.heap_lang Require Import proofmode notation par spin_lock.
From mathcomp Require Import seq fintype.

Module Type SKIPLIST_PARAMS.
  Parameter INT_MIN : Z.
  Parameter INT_MAX : Z.
  Parameter (HMIN_MAX: INT_MIN < INT_MAX).
End SKIPLIST_PARAMS.

Definition node_rep : Type := Z * loc * val * val.
Definition node_key (n: node_rep) : Z := n.1.1.1.
Definition node_next (n: node_rep) : loc := n.1.1.2.
Definition node_val (n: node_rep) : val := n.1.2.
Definition node_lock (n: node_rep) : val := n.2.

Definition nodeKey : val := λ: "l", Fst "l".
Definition nodeNext : val := λ: "l", Fst (Snd "l").
Definition nodeVal : val := λ: "l", Fst (Snd (Snd "l")).
Definition nodeLock : val := λ: "l", Snd (Snd (Snd "l")).

Definition rep_to_node (n: node_rep) : val :=
  (#(node_key n), (#(node_next n), (node_val n, (node_lock n)))).

Lemma fold_rep_to_node np':
  ((#(node_key np'), (#(node_next np'), (node_val np', (node_lock np')))))%E =
  rep_to_node np'.
Proof. done. Qed.


Module Skiplist (Params: SKIPLIST_PARAMS).
  Import Params.
  
  Definition right_sentinel : node_rep :=
    (INT_MAX, xH, #(), #(LitLoc xH)).

  Definition findPred_aux : val :=
    rec: "findPred" "count" "pred" "k" :=
      let: "curr" := !(nodeNext "pred") in
      let: "ck" := (nodeKey "curr") in
      if: "k" ≤ "ck"
      then ("pred", ("ck", "count" + #1))
      else "findPred" ("count" + #1) "curr" "k".
  
  Definition findPred : val :=
    λ: "pred" "k", findPred_aux #0 "pred" "k".
  
  Definition findLockPred: val :=
    rec: "findPred" "pred" "k" :=
      let: "curr" := !(nodeNext "pred") in
      let: "ck" := (nodeKey "curr") in
      if: "k" ≤ "ck"
      then
        acquire (nodeLock "pred");;
        let: "curr'" := !(nodeNext "pred") in
        if: "curr" = "curr'"
        then ("pred", "ck")
        else
          release (nodeLock "pred");;
          "findPred" "pred" "k"
      else "findPred" "curr" "k".

  Definition newSkipList : val :=
    λ: <>,
         let: "bottomLeft" := (#INT_MIN, (ref (rep_to_node (right_sentinel)),
                                          (#(), newlock #()))) in
         let: "topLeft" := (#INT_MIN, (ref (rep_to_node (right_sentinel)),
                                       ("bottomLeft", newlock #()))) in
         "topLeft".
  
  Definition memSkipList : val :=
    λ: "l" "k",
    let: "top" := findPred "l" "k" in
    let: "predTop" := Fst "top" in
    let: "ck_top" := Fst (Snd "top") in
    let: "count_top" := Snd (Snd "top") in
    if: ("ck_top" = "k") then
      (#true, "count_top")
    else
      let: "bottom" := findPred (nodeVal "predTop") "k" in
      let: "predBottom" := Fst "bottom" in
      let: "ck_bot" := Fst (Snd "bottom") in
      let: "count_bot" := Snd (Snd "bottom") in
      ("ck_bot" = "k", "count_top" + "count_bot").
  
  Definition addSkipList : val :=
    λ: "l" "k",
    let: "top" := findLockPred "l" "k" in
    let: "predTop" := Fst "top" in
    let: "ck_top" := Snd "top" in
    if: ("ck_top" = "k") then
      (* Node Already in List *)
      release (nodeLock "predTop")
    else
      let: "bottom" := findLockPred (nodeVal "predTop") "k" in
      let: "predBottom" := Fst "bottom" in
      let: "ck_bot" := Snd "bottom" in
      (if: ("ck_bot" = "k") then
        #()
        (* Node Already in List *)
      else
        let: "bottomNode" := ("k", (ref !(nodeNext "predBottom"), (#(), newlock #()))) in
        (if: flip #1 #2 = #true then
          (nodeNext "predBottom") <- "bottomNode";;
          let: "topNode" := ("k", (ref !(nodeNext "predTop"), ("bottomNode", newlock #()))) in
          (nodeNext "predTop") <- "topNode"
         else
          (nodeNext "predBottom") <- "bottomNode"));;
      release (nodeLock "predTop");;
      release (nodeLock "predBottom").
End Skiplist.
