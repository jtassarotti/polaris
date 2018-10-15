From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang.lib.barrier Require Import proof.
From iris.heap_lang Require Import par.
From iris.heap_lang Require Import adequacy proofmode.
Set Default Proof Using "Type".

Definition worker (n : Z) : val :=
  λ: "b" "y", wait "b" ;; !"y" #n.
Definition client : expr :=
  let: "y" := ref #0 in
  let: "b" := newbarrier #() in
  ("y" <- (λ: "z", "z" + #42) ;; signal "b") |||
    (worker 12 "b" "y" ||| worker 17 "b" "y").

Section client.
  Local Set Default Proof Using "Type*".
  Context `{!heapG Σ, !probG Σ, !barrierG Σ, !spawnG Σ}.

  Definition N := nroot .@ "barrier".

  Definition y_inv (q : Qp) (l : loc) : iProp Σ :=
    (∃ f : val, l ↦{q} f ∗ □ ∀ n : Z, WP f #n {{ v, ⌜v = #(n + 42)⌝ }})%I.

  Lemma y_inv_split q l : y_inv q l -∗ (y_inv (q/2) l ∗ y_inv (q/2) l).
  Proof.
    iDestruct 1 as (f) "[[Hl1 Hl2] #Hf]".
    iSplitL "Hl1"; iExists f; by iSplitL; try iAlways.
  Qed.

  Lemma worker_safe q (n : Z) (b y : loc) :
    recv N b (y_inv q y) -∗ WP worker n #b #y {{ _, True }}.
  Proof.
    iIntros "Hrecv". wp_lam. wp_let.
    wp_apply (wait_spec with "Hrecv"). iDestruct 1 as (f) "[Hy #Hf]".
    wp_seq. wp_load.
    iApply (wp_wand with "[]"). iApply "Hf". by iIntros (v) "_".
  Qed.

  Lemma client_safe : WP client {{ _, True }}%I.
  Proof.
    iIntros ""; rewrite /client. wp_alloc y as "Hy". wp_let.
    wp_apply (newbarrier_spec N (y_inv 1 y) with "[//]").
    iIntros (l) "[Hr Hs]". wp_let.
    iApply (wp_par (λ _, True%I) (λ _, True%I) with "[Hy Hs] [Hr]"); last auto.
    - (* The original thread, the sender. *)
      wp_store. iApply (signal_spec with "[-]"); last by iNext; auto.
      iSplitR "Hy"; first by eauto.
      iExists _; iSplitL; [done|]. iIntros "!#" (n). wp_let. by wp_op.
    - (* The two spawned threads, the waiters. *)
      iDestruct (recv_weaken with "[] Hr") as "Hr".
      { iIntros "Hy". by iApply (y_inv_split with "Hy"). }
      iMod (recv_split with "Hr") as "[H1 H2]"; first done.
      iApply (wp_par (λ _, True%I) (λ _, True%I) with "[H1] [H2]"); last auto.
      + by iApply worker_safe.
      + by iApply worker_safe.
Qed.
End client.

Section ClosedProofs.

Let Σ : gFunctors := #[ heapΣ ; barrierΣ ; spawnΣ ].

Lemma client_adequate σ : adequate client σ (λ _, True).
Proof. apply (heap_adequacy' Σ)=> ??. apply client_safe. Qed.

End ClosedProofs.
