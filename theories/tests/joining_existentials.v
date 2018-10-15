From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.algebra Require Import excl agree csum.
From iris.heap_lang.lib.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par proofmode.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Definition one_shotR (Σ : gFunctors) (F : cFunctor) :=
  csumR (exclR unitC) (agreeR $ laterC $ F (iPreProp Σ)).
Definition Pending {Σ F} : one_shotR Σ F := Cinl (Excl ()).
Definition Shot {Σ} {F : cFunctor} (x : F (iProp Σ)) : one_shotR Σ F :=
  Cinr $ to_agree $ Next $ cFunctor_map F (iProp_fold, iProp_unfold) x.

Class oneShotG (Σ : gFunctors) (F : cFunctor) :=
  one_shot_inG :> inG Σ (one_shotR Σ F).
Definition oneShotΣ (F : cFunctor) : gFunctors :=
  #[ GFunctor (csumRF (exclRF unitC) (agreeRF (▶ F))) ].
Instance subG_oneShotΣ {Σ F} : subG (oneShotΣ F) Σ → oneShotG Σ F.
Proof. solve_inG. Qed.

Definition client eM eW1 eW2 : expr :=
  let: "b" := newbarrier #() in
  (eM ;; signal "b") ||| ((wait "b" ;; eW1) ||| (wait "b" ;; eW2)).

Section proof.
Local Set Default Proof Using "Type*".
Context `{!heapG Σ, !probG Σ, !barrierG Σ, !spawnG Σ, !oneShotG Σ F}.
Context (N : namespace).
Local Notation X := (F (iProp Σ)).

Definition barrier_res γ (Φ : X → iProp Σ) : iProp Σ :=
  (∃ x, own γ (Shot x) ∗ Φ x)%I.

Lemma worker_spec e γ l (Φ Ψ : X → iProp Σ) `{!Closed [] e} :
  recv N l (barrier_res γ Φ) -∗ (∀ x, {{ Φ x }} e {{ _, Ψ x }}) -∗
  WP wait #l ;; e {{ _, barrier_res γ Ψ }}.
Proof.
  iIntros "Hl #He". wp_apply (wait_spec with "[- $Hl]"); simpl.
  iDestruct 1 as (x) "[#Hγ Hx]".
  wp_seq. iApply (wp_wand with "[Hx]"); [by iApply "He"|].
  iIntros (v) "?"; iExists x; by iSplit.
Qed.

Context (P : iProp Σ) (Φ Φ1 Φ2 Ψ Ψ1 Ψ2 : X -n> iProp Σ).
Context {Φ_split : ∀ x, Φ x -∗ (Φ1 x ∗ Φ2 x)}.
Context {Ψ_join  : ∀ x, Ψ1 x -∗ Ψ2 x -∗ Ψ x}.

Lemma P_res_split γ : barrier_res γ Φ -∗ barrier_res γ Φ1 ∗ barrier_res γ Φ2.
Proof.
  iDestruct 1 as (x) "[#Hγ Hx]".
  iDestruct (Φ_split with "Hx") as "[H1 H2]". by iSplitL "H1"; iExists x; iSplit.
Qed.

Lemma Q_res_join γ : barrier_res γ Ψ1 -∗ barrier_res γ Ψ2 -∗ ▷ barrier_res γ Ψ.
Proof.
  iDestruct 1 as (x) "[#Hγ Hx]"; iDestruct 1 as (x') "[#Hγ' Hx']".
  iAssert (▷ (x ≡ x'))%I as "Hxx".
  { iCombine "Hγ" "Hγ'" as "Hγ2". iClear "Hγ Hγ'".
    rewrite own_valid csum_validI /= agree_validI agree_equivI uPred.later_equivI /=.
    rewrite -{2}[x]cFunctor_id -{2}[x']cFunctor_id.
    rewrite (ne_proper (cFunctor_map F) (cid, cid) (_ ◎ _, _ ◎ _)); last first.
    { by split; intro; simpl; symmetry; apply iProp_fold_unfold. }
    rewrite !cFunctor_compose. iNext. by iRewrite "Hγ2". }
  iNext. iRewrite -"Hxx" in "Hx'".
  iExists x; iFrame "Hγ". iApply (Ψ_join with "Hx Hx'").
Qed.

Lemma client_spec_new eM eW1 eW2 `{!Closed [] eM, !Closed [] eW1, !Closed [] eW2} :
  P -∗
  {{ P }} eM {{ _, ∃ x, Φ x }} -∗
  (∀ x, {{ Φ1 x }} eW1 {{ _, Ψ1 x }}) -∗
  (∀ x, {{ Φ2 x }} eW2 {{ _, Ψ2 x }}) -∗
  WP client eM eW1 eW2 {{ _, ∃ γ, barrier_res γ Ψ }}.
Proof using All.
  iIntros "/= HP #He #He1 #He2"; rewrite /client.
  iMod (own_alloc (Pending : one_shotR Σ F)) as (γ) "Hγ"; first done.
  wp_apply (newbarrier_spec N (barrier_res γ Φ)); auto.
  iIntros (l) "[Hr Hs]".
  set (workers_post (v : val) := (barrier_res γ Ψ1 ∗ barrier_res γ Ψ2)%I).
  wp_let. wp_apply (wp_par  (λ _, True)%I workers_post with "[HP Hs Hγ] [Hr]").
  - wp_bind eM. iApply (wp_wand with "[HP]"); [by iApply "He"|].
    iIntros (v) "HP"; iDestruct "HP" as (x) "HP". wp_let.
    iMod (own_update with "Hγ") as "Hx".
    { by apply (cmra_update_exclusive (Shot x)). }
    iApply (signal_spec with "[- $Hs]"); last auto.
    iExists x; auto.
  - iDestruct (recv_weaken with "[] Hr") as "Hr"; first by iApply P_res_split.
    iMod (recv_split with "Hr") as "[H1 H2]"; first done.
    wp_apply (wp_par (λ _, barrier_res γ Ψ1)%I
                     (λ _, barrier_res γ Ψ2)%I with "[H1] [H2]").
    + iApply (worker_spec with "H1"); auto.
    + iApply (worker_spec with "H2"); auto.
    + auto.
  - iIntros (_ v) "[_ [H1 H2]]". iDestruct (Q_res_join with "H1 H2") as "?". auto.
Qed.
End proof.
