From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Module invG.
  Class invG (Σ : gFunctors) : Set := WsatG {
    inv_inG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
    enabled_inG :> inG Σ coPset_disjR;
    disabled_inG :> inG Σ (gset_disjR positive);
    invariant_name : gname;
    enabled_name : gname;
    disabled_name : gname;
  }.
End invG.
Import invG.

Definition invariant_unfold {Σ} (P : iProp Σ) : agree (later (iPreProp Σ)) :=
  to_agree (Next (iProp_unfold P)).
Definition ownI `{invG Σ} (i : positive) (P : iProp Σ) : iProp Σ :=
  own invariant_name (◯ {[ i := invariant_unfold P ]}).
Arguments ownI {_ _} _ _%I.
Typeclasses Opaque ownI.
Instance: Params (@invariant_unfold) 1.
Instance: Params (@ownI) 3.

Definition ownE `{invG Σ} (E : coPset) : iProp Σ :=
  own enabled_name (CoPset E).
Typeclasses Opaque ownE.
Instance: Params (@ownE) 3.

Definition ownD `{invG Σ} (E : gset positive) : iProp Σ :=
  own disabled_name (GSet E).
Typeclasses Opaque ownD.
Instance: Params (@ownD) 3.

Definition wsat `{invG Σ} : iProp Σ :=
  locked (∃ I : gmap positive (iProp Σ),
    own invariant_name (● (invariant_unfold <$> I : gmap _ _)) ∗
    [∗ map] i ↦ Q ∈ I, ▷ Q ∗ ownD {[i]} ∨ ownE {[i]})%I.

Section wsat.
Context `{invG Σ}.
Implicit Types P : iProp Σ.

(* Invariants *)
Instance invariant_unfold_contractive : Contractive (@invariant_unfold Σ).
Proof. solve_contractive. Qed.
Global Instance ownI_contractive i : Contractive (@ownI Σ _ i).
Proof. solve_contractive. Qed.
Global Instance ownI_persistent i P : Persistent (ownI i P).
Proof. rewrite /ownI. apply _. Qed.

Lemma ownE_empty : (|==> ownE ∅)%I.
Proof. by rewrite /uPred_valid (own_unit (coPset_disjUR) enabled_name). Qed.
Lemma ownE_op E1 E2 : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof. intros. by rewrite /ownE -own_op coPset_disj_union. Qed.
Lemma ownE_disjoint E1 E2 : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownE -own_op own_valid. by iIntros (?%coPset_disj_valid_op). Qed.
Lemma ownE_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownE_op|].
  iIntros "HE". iDestruct (ownE_disjoint with "HE") as %?.
  iSplit; first done. iApply ownE_op; by try iFrame.
Qed.
Lemma ownE_singleton_twice i : ownE {[i]} ∗ ownE {[i]} ⊢ False.
Proof. rewrite ownE_disjoint. iIntros (?); set_solver. Qed.

Lemma ownD_empty : (|==> ownD ∅)%I.
Proof. by rewrite /uPred_valid (own_unit (gset_disjUR positive) disabled_name). Qed.
Lemma ownD_op E1 E2 : E1 ## E2 → ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof. intros. by rewrite /ownD -own_op gset_disj_union. Qed.
Lemma ownD_disjoint E1 E2 : ownD E1 ∗ ownD E2 ⊢ ⌜E1 ## E2⌝.
Proof. rewrite /ownD -own_op own_valid. by iIntros (?%gset_disj_valid_op). Qed.
Lemma ownD_op' E1 E2 : ⌜E1 ## E2⌝ ∧ ownD (E1 ∪ E2) ⊣⊢ ownD E1 ∗ ownD E2.
Proof.
  iSplit; [iIntros "[% ?]"; by iApply ownD_op|].
  iIntros "HE". iDestruct (ownD_disjoint with "HE") as %?.
  iSplit; first done. iApply ownD_op; by try iFrame.
Qed.
Lemma ownD_singleton_twice i : ownD {[i]} ∗ ownD {[i]} ⊢ False.
Proof. rewrite ownD_disjoint. iIntros (?); set_solver. Qed.

Lemma invariant_lookup (I : gmap positive (iProp Σ)) i P :
  own invariant_name (● (invariant_unfold <$> I : gmap _ _)) ∗
  own invariant_name (◯ {[i := invariant_unfold P]}) ⊢
  ∃ Q, ⌜I !! i = Some Q⌝ ∗ ▷ (Q ≡ P).
Proof.
  rewrite -own_op own_valid auth_validI /=. iIntros "[#HI #HvI]".
  iDestruct "HI" as (I') "HI". rewrite gmap_equivI gmap_validI.
  iSpecialize ("HI" $! i). iSpecialize ("HvI" $! i).
  rewrite left_id_L lookup_fmap lookup_op lookup_singleton uPred.option_equivI.
  case: (I !! i)=> [Q|] /=; [|case: (I' !! i)=> [Q'|] /=; by iExFalso].
  iExists Q; iSplit; first done.
  iAssert (invariant_unfold Q ≡ invariant_unfold P)%I as "?".
  { case: (I' !! i)=> [Q'|] //=.
    iRewrite "HI" in "HvI". rewrite uPred.option_validI agree_validI.
    iRewrite -"HvI" in "HI". by rewrite agree_idemp. }
  rewrite /invariant_unfold.
  by rewrite agree_equivI uPred.later_equivI iProp_unfold_equivI.
Qed.

Lemma ownI_open i P : wsat ∗ ownI i P ∗ ownE {[i]} ⊢ wsat ∗ ▷ P ∗ ownD {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HiE)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup I i P with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ $]|HiE'] HI]"; eauto.
  - iSplitR "HQ"; last by iNext; iRewrite -"HPQ".
    iExists I. iFrame "Hw". iApply (big_opM_delete _ _ i); eauto.
    iFrame "HI"; eauto.
  - iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as %[].
Qed.
Lemma ownI_close i P : wsat ∗ ownI i P ∗ ▷ P ∗ ownD {[i]} ⊢ wsat ∗ ownE {[i]}.
Proof.
  rewrite /ownI /wsat -!lock.
  iIntros "(Hw & Hi & HP & HiD)". iDestruct "Hw" as (I) "[Hw HI]".
  iDestruct (invariant_lookup with "[$]") as (Q ?) "#HPQ".
  iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ ?]|$] HI]"; eauto.
  - iDestruct (ownD_singleton_twice with "[$]") as %[].
  - iExists I. iFrame "Hw". iApply (big_opM_delete _ _ i); eauto.
    iFrame "HI". iLeft. iFrame "HiD". by iNext; iRewrite "HPQ".
Qed.

Lemma ownI_alloc φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ∗ ▷ P ==∗ ∃ i, ⌜φ i⌝ ∗ wsat ∗ ownI i P.
Proof.
  iIntros (Hfresh) "[Hw HP]". rewrite /wsat -!lock.
  iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
  iMod (own_updateP with "[$]") as "HE".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HE" as (X) "[Hi HE]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold P)); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi. }
  iApply (big_opM_insert _ I); first done.
  iFrame "HI". iLeft. by rewrite /ownD; iFrame.
Qed.

Lemma ownI_alloc_open φ P :
  (∀ E : gset positive, ∃ i, i ∉ E ∧ φ i) →
  wsat ==∗ ∃ i, ⌜φ i⌝ ∗ (ownE {[i]} -∗ wsat) ∗ ownI i P ∗ ownD {[i]}.
Proof.
  iIntros (Hfresh) "Hw". rewrite /wsat -!lock. iDestruct "Hw" as (I) "[Hw HI]".
  iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
  iMod (own_updateP with "[$]") as "HD".
  { apply (gset_disj_alloc_empty_updateP_strong' (λ i, I !! i = None ∧ φ i)).
    intros E. destruct (Hfresh (E ∪ dom _ I))
      as (i & [? HIi%not_elem_of_dom]%not_elem_of_union & ?); eauto. }
  iDestruct "HD" as (X) "[Hi HD]"; iDestruct "Hi" as %(i & -> & HIi & ?).
  iMod (own_update with "Hw") as "[Hw HiP]".
  { eapply auth_update_alloc,
     (alloc_singleton_local_update _ i (invariant_unfold P)); last done.
    by rewrite /= lookup_fmap HIi. }
  iModIntro; iExists i;  iSplit; [done|]. rewrite /ownI; iFrame "HiP".
  rewrite -/(ownD _). iFrame "HD".
  iIntros "HE". iExists (<[i:=P]>I); iSplitL "Hw".
  { by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi. }
  iApply (big_opM_insert _ I); first done.
  iFrame "HI". by iRight.
Qed.
End wsat.
