(** Correctness of in-place list reversal *)
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Section list_reverse.
Context `{!heapG Σ, probG Σ}.
Implicit Types l : loc.

Fixpoint is_list (hd : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
  end%I.

Definition rev : val :=
  rec: "rev" "hd" "acc" :=
    match: "hd" with
      NONE => "acc"
    | SOME "l" =>
       let: "tmp1" := Fst !"l" in
       let: "tmp2" := Snd !"l" in
       "l" <- ("tmp1", "acc");;
       "rev" "tmp2" "hd"
    end.

Lemma rev_acc_wp hd acc xs ys :
  {{{ is_list hd xs ∗ is_list acc ys }}}
    rev hd acc
  {{{ w, RET w; is_list w (reverse xs ++ ys) }}}.
Proof.
  iIntros (Φ) "[Hxs Hys] HΦ".
  iLöb as "IH" forall (hd acc xs ys Φ). wp_rec. wp_let.
  destruct xs as [|x xs]; iSimplifyEq.
  - wp_match. by iApply "HΦ".
  - iDestruct "Hxs" as (l hd' ->) "[Hx Hxs]".
    wp_match. wp_load. wp_proj. wp_let. wp_load. wp_proj. wp_let. wp_store.
    iApply ("IH" $! hd' (SOMEV #l) xs (x :: ys) with "Hxs [Hx Hys]"); simpl.
    { iExists l, acc; by iFrame. }
    iNext. iIntros (w). rewrite cons_middle assoc -reverse_cons. iApply "HΦ".
Qed.

Lemma rev_wp hd xs :
  {{{ is_list hd xs }}} rev hd (InjL #()) {{{ w, RET w; is_list w (reverse xs) }}}.
Proof.
  iIntros (Φ) "Hxs HΦ".
  iApply (rev_acc_wp hd NONEV xs [] with "[$Hxs //]").
  iNext; iIntros (w). rewrite right_id_L. iApply "HΦ".
Qed.
End list_reverse.
