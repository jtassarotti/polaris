From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang.lib.barrier Require Export barrier.
From stdpp Require Import functions.
From iris.base_logic Require Import big_op lib.saved_prop lib.sts.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib.barrier Require Import protocol.
Set Default Proof Using "Type".

(** The CMRAs/functors we need. *)
Class barrierG Σ := BarrierG {
  barrier_stsG :> stsG Σ sts;
  barrier_savedPropG :> savedPropG Σ idCF;
}.
Definition barrierΣ : gFunctors := #[stsΣ sts; savedPropΣ idCF].

Instance subG_barrierΣ {Σ} : subG barrierΣ Σ → barrierG Σ.
Proof. solve_inG. Qed.

(** Now we come to the Iris part of the proof. *)
Section proof.
Context `{!heapG Σ, !probG Σ, !barrierG Σ} (N : namespace).
Implicit Types I : gset gname.

Definition ress (P : iProp Σ) (I : gset gname) : iProp Σ :=
  (∃ Ψ : gname → iProp Σ,
    ▷ (P -∗ [∗ set] i ∈ I, Ψ i) ∗ [∗ set] i ∈ I, saved_prop_own i (Ψ i))%I.

Coercion state_to_val (s : state) : val :=
  match s with State Low _ => #false | State High _ => #true end.
Arguments state_to_val !_ / : simpl nomatch.

Definition state_to_prop (s : state) (P : iProp Σ) : iProp Σ :=
  match s with State Low _ => P | State High _ => True%I end.
Arguments state_to_prop !_ _ / : simpl nomatch.

Definition barrier_inv (l : loc) (P : iProp Σ) (s : state) : iProp Σ :=
  (l ↦ s ∗ ress (state_to_prop s P) (state_I s))%I.

Definition barrier_ctx (γ : gname) (l : loc) (P : iProp Σ) : iProp Σ :=
  sts_ctx γ N (barrier_inv l P).

Definition send (l : loc) (P : iProp Σ) : iProp Σ :=
  (∃ γ, barrier_ctx γ l P ∗ sts_ownS γ low_states {[ Send ]})%I.

Definition recv (l : loc) (R : iProp Σ) : iProp Σ :=
  (∃ γ P Q i,
    barrier_ctx γ l P ∗ sts_ownS γ (i_states i) {[ Change i ]} ∗
    saved_prop_own i Q ∗ ▷ (Q -∗ R))%I.

Global Instance barrier_ctx_persistent (γ : gname) (l : loc) (P : iProp Σ) :
  PersistentP (barrier_ctx γ l P).
Proof. apply _. Qed.

(** Setoids *)
Global Instance ress_ne n : Proper (dist n ==> (=) ==> dist n) ress.
Proof. solve_proper. Qed.
Global Instance state_to_prop_ne s :
  NonExpansive (state_to_prop s).
Proof. solve_proper. Qed.
Global Instance barrier_inv_ne n l :
  Proper (dist n ==> eq ==> dist n) (barrier_inv l).
Proof. solve_proper. Qed.
Global Instance barrier_ctx_ne γ l : NonExpansive (barrier_ctx γ l).
Proof. solve_proper. Qed. 
Global Instance send_ne l : NonExpansive (send l).
Proof. solve_proper. Qed.
Global Instance recv_ne l : NonExpansive (recv l).
Proof. solve_proper. Qed.

(** Helper lemmas *)
Lemma ress_split i i1 i2 Q R1 R2 P I :
  i ∈ I → i1 ∉ I → i2 ∉ I → i1 ≠ i2 →
  saved_prop_own i Q -∗ saved_prop_own i1 R1 -∗ saved_prop_own i2 R2 -∗
  (Q -∗ R1 ∗ R2) -∗ ress P I -∗
  ress P ({[i1;i2]} ∪ I ∖ {[i]}).
Proof.
  iIntros (????) "#HQ #H1 #H2 HQR"; iDestruct 1 as (Ψ) "[HPΨ HΨ]".
  iDestruct (big_opS_delete _ _ i with "HΨ") as "[#HΨi HΨ]"; first done.
  iExists (<[i1:=R1]> (<[i2:=R2]> Ψ)). iSplitL "HQR HPΨ".
  - iPoseProof (saved_prop_agree with "HQ HΨi") as "#Heq".
    iNext. iRewrite "Heq" in "HQR". iIntros "HP". iSpecialize ("HPΨ" with "HP").
    iDestruct (big_opS_delete _ _ i with "HPΨ") as "[HΨ HPΨ]"; first done.
    iDestruct ("HQR" with "HΨ") as "[HR1 HR2]".
    rewrite -assoc_L !big_opS_fn_insert'; [|abstract set_solver ..].
    by iFrame.
  - rewrite -assoc_L !big_opS_fn_insert; [|abstract set_solver ..]. eauto.
Qed.

(** Actual proofs *)
Lemma newbarrier_spec (P : iProp Σ) :
  {{{ True }}} newbarrier #() {{{ l, RET #l; recv l P ∗ send l P }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite -wp_fupd /newbarrier /=. wp_seq. wp_alloc l as "Hl".
  iApply ("HΦ" with "[> -]").
  iMod (saved_prop_alloc (F:=idCF) P) as (γ) "#?".
  iMod (sts_alloc (barrier_inv l P) _ N (State Low {[ γ ]}) with "[-]")
    as (γ') "[#? Hγ']"; eauto.
  { iNext. rewrite /barrier_inv /=. iFrame.
    iExists (const P). rewrite !big_opS_singleton /=. eauto. }
  iAssert (barrier_ctx γ' l P)%I as "#?".
  { done. }
  iAssert (sts_ownS γ' (i_states γ) {[Change γ]}
    ∗ sts_ownS γ' low_states {[Send]})%I with "[> -]" as "[Hr Hs]".
  { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
    - set_solver.
    - iApply (sts_own_weaken with "Hγ'");
        auto using sts.closed_op, i_states_closed, low_states_closed;
        abstract set_solver. }
  iModIntro. iSplitL "Hr".
  - iExists γ', P, P, γ. iFrame. auto.
  - rewrite /send. auto.
Qed.

Lemma signal_spec l P :
  {{{ send l P ∗ P }}} signal #l {{{ RET #(); True }}}.
Proof.
  rewrite /signal /=.
  iIntros (Φ) "[Hs HP] HΦ". iDestruct "Hs" as (γ) "[#Hsts Hγ]". wp_let.
  iMod (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  destruct p; [|done]. wp_store.
  iSpecialize ("HΦ" with "[#]") => //. iFrame "HΦ".
  iMod ("Hclose" $! (State High I) (∅ : set token) with "[-]"); last done.
  iSplit; [iPureIntro; by eauto using signal_step|].
  rewrite /barrier_inv /ress /=. iNext. iFrame "Hl".
  iDestruct "Hr" as (Ψ) "[Hr Hsp]"; iExists Ψ; iFrame "Hsp".
  iNext. iIntros "_"; by iApply "Hr".
Qed.

Lemma wait_spec l P:
  {{{ recv l P }}} wait #l {{{ RET #(); P }}}.
Proof.
  rename P into R.
  iIntros (Φ) "Hr HΦ"; iDestruct "Hr" as (γ P Q i) "(#Hsts & Hγ & #HQ & HQR)".
  iLöb as "IH". wp_rec. wp_bind (! _)%E.
  iMod (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  wp_load. destruct p.
  - iMod ("Hclose" $! (State Low I) {[ Change i ]} with "[Hl Hr]") as "Hγ".
    { iSplit; first done. rewrite /barrier_inv /=. by iFrame. }
    iAssert (sts_ownS γ (i_states i) {[Change i]})%I with "[> Hγ]" as "Hγ".
    { iApply (sts_own_weaken with "Hγ"); eauto using i_states_closed. }
    iModIntro. wp_if.
    iApply ("IH" with "Hγ [HQR] [HΦ]"); auto.
  - (* a High state: the comparison succeeds, and we perform a transition and
    return to the client *)
    iDestruct "Hr" as (Ψ) "[HΨ Hsp]".
    iDestruct (big_opS_delete _ _ i with "Hsp") as "[#HΨi Hsp]"; first done.
    iAssert (▷ Ψ i ∗ ▷ [∗ set] j ∈ I ∖ {[i]}, Ψ j)%I with "[HΨ]" as "[HΨ HΨ']".
    { iNext. iApply (big_opS_delete _ _ i); first done. by iApply "HΨ". }
    iMod ("Hclose" $! (State High (I ∖ {[ i ]})) ∅ with "[HΨ' Hl Hsp]").
    { iSplit; [iPureIntro; by eauto using wait_step|].
      rewrite /barrier_inv /=. iNext. iFrame "Hl". iExists Ψ; iFrame. auto. }
    iPoseProof (saved_prop_agree with "HQ HΨi") as "#Heq".
    iModIntro. wp_if.
    iApply "HΦ". iApply "HQR". by iRewrite "Heq".
Qed.

Lemma recv_split E l P1 P2 :
  ↑N ⊆ E → recv l (P1 ∗ P2) ={E}=∗ recv l P1 ∗ recv l P2.
Proof.
  rename P1 into R1; rename P2 into R2.
  iIntros (?). iDestruct 1 as (γ P Q i) "(#Hsts & Hγ & #HQ & HQR)".
  iMod (sts_openS (barrier_inv l P) _ _ γ with "[Hγ]")
    as ([p I]) "(% & [Hl Hr] & Hclose)"; eauto.
  iMod (saved_prop_alloc_strong (R1: ∙%CF (iProp Σ)) I) as (i1) "[% #Hi1]".
  iMod (saved_prop_alloc_strong (R2: ∙%CF (iProp Σ)) (I ∪ {[i1]}))
    as (i2) "[Hi2' #Hi2]"; iDestruct "Hi2'" as %Hi2.
  rewrite ->not_elem_of_union, elem_of_singleton in Hi2; destruct Hi2.
  iMod ("Hclose" $! (State p ({[i1; i2]} ∪ I ∖ {[i]}))
                    {[Change i1; Change i2 ]} with "[-]") as "Hγ".
  { iSplit; first by eauto using split_step.
    rewrite /barrier_inv /=. iNext. iFrame "Hl".
    by iApply (ress_split with "HQ Hi1 Hi2 HQR"). }
  iAssert (sts_ownS γ (i_states i1) {[Change i1]}
    ∗ sts_ownS γ (i_states i2) {[Change i2]})%I with "[> -]" as "[Hγ1 Hγ2]".
  { iApply sts_ownS_op; eauto using i_states_closed, low_states_closed.
    - abstract set_solver.
    - iApply (sts_own_weaken with "Hγ");
        eauto using sts.closed_op, i_states_closed.
      abstract set_solver. }
  iModIntro; iSplitL "Hγ1".
  - iExists γ, P, R1, i1. iFrame; auto.
  - iExists γ, P, R2, i2. iFrame; auto.
Qed.

Lemma recv_weaken l P1 P2 : (P1 -∗ P2) -∗ recv l P1 -∗ recv l P2.
Proof.
  iIntros "HP". iDestruct 1 as (γ P Q i) "(#Hctx&Hγ&Hi&HP1)".
  iExists γ, P, Q, i. iFrame "Hctx Hγ Hi".
  iNext. iIntros "HQ". by iApply "HP"; iApply "HP1".
Qed.

Lemma recv_mono l P1 P2 : (P1 ⊢ P2) → recv l P1 ⊢ recv l P2.
Proof. iIntros (HP) "H". iApply (recv_weaken with "[] H"). iApply HP. Qed.
End proof.

Typeclasses Opaque barrier_ctx send recv.
