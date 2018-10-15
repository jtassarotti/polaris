From iris.base_logic Require Import base_logic soundness.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type*".

(** This proves that we need the ▷ in a "Saved Proposition" construction with
name-dependent allocation. *)
Module savedprop. Section savedprop.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Notation "¬ P" := (□ (P → False))%I : uPred_scope.
  Implicit Types P : iProp.

  (** Saved Propositions and the update modality *)
  Context (sprop : Type) (saved : sprop → iProp → iProp).
  Hypothesis sprop_persistent : ∀ i P, Persistent (saved i P).
  Hypothesis sprop_alloc_dep :
    ∀ (P : sprop → iProp), (|==> (∃ i, saved i (P i)))%I.
  Hypothesis sprop_agree : ∀ i P Q, saved i P ∧ saved i Q ⊢ □ (P ↔ Q).

  (** A bad recursive reference: "Assertion with name [i] does not hold" *)
  Definition A (i : sprop) : iProp := ∃ P, ¬ P ∗ saved i P.

  Lemma A_alloc : (|==> ∃ i, saved i (A i))%I.
  Proof. by apply sprop_alloc_dep. Qed.

  Lemma saved_NA i : saved i (A i) ⊢ ¬ A i.
  Proof.
    iIntros "#Hs !# #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "[#HNP HsP]". iApply "HNP".
    iDestruct (sprop_agree i P (A i) with "[]") as "#[_ HP]".
    { eauto. }
    iApply "HP". done.
  Qed.

  Lemma saved_A i : saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hs". iExists (A i). iFrame "#".
    by iApply saved_NA.
  Qed.

  Lemma contradiction : False.
  Proof using All.
    apply (@consistency M); simpl.
    iIntros "". iMod A_alloc as (i) "#H".
    iPoseProof (saved_NA with "H") as "HN".
    iApply "HN". by iApply saved_A.
  Qed.
End savedprop. End savedprop.

(** This proves that we need the ▷ when opening invariants. *)
(** We fork in [uPred M] for any M, but the proof would work in any BI. *)
Module inv. Section inv.
  Context (M : ucmraT).
  Notation iProp := (uPred M).
  Implicit Types P : iProp.

  (** Assumptions *)
  (** We have the update modality (two classes: empty/full mask) *)
  Inductive mask := M0 | M1.
  Context (fupd : mask → iProp → iProp).

  Hypothesis fupd_intro : ∀ E P, P ⊢ fupd E P.
  Hypothesis fupd_mono : ∀ E P Q, (P ⊢ Q) → fupd E P ⊢ fupd E Q.
  Hypothesis fupd_fupd : ∀ E P, fupd E (fupd E P) ⊢ fupd E P.
  Hypothesis fupd_frame_l : ∀ E P Q, P ∗ fupd E Q ⊢ fupd E (P ∗ Q).
  Hypothesis fupd_mask_mono : ∀ P, fupd M0 P ⊢ fupd M1 P.

  (** We have invariants *)
  Context (name : Type) (inv : name → iProp → iProp).
  Hypothesis inv_persistent : ∀ i P, Persistent (inv i P).
  Hypothesis inv_alloc : ∀ P, P ⊢ fupd M1 (∃ i, inv i P).
  Hypothesis inv_open :
    ∀ i P Q R, (P ∗ Q ⊢ fupd M0 (P ∗ R)) → (inv i P ∗ Q ⊢ fupd M1 R).

  (* We have tokens for a little "two-state STS": [start] -> [finish].
     state. [start] also asserts the exact state; it is only ever owned by the
     invariant.  [finished] is duplicable. *)
  (* Posssible implementations of these axioms:
     * Using the STS monoid of a two-state STS, where [start] is the
       authoritative saying the state is exactly [start], and [finish]
       is the "we are at least in state [finish]" typically owned by threads.
     * Ex () +_## ()
  *)
  Context (gname : Type).
  Context (start finished : gname → iProp).

  Hypothesis sts_alloc : fupd M0 (∃ γ, start γ).
  Hypotheses start_finish : ∀ γ, start γ ⊢ fupd M0 (finished γ).

  Hypothesis finished_not_start : ∀ γ, start γ ∗ finished γ ⊢ False.

  Hypothesis finished_dup : ∀ γ, finished γ ⊢ finished γ ∗ finished γ.

  (** We assume that we cannot update to false. *)
  Hypothesis consistency : ¬ (fupd M1 False).

  (** Some general lemmas and proof mode compatibility. *)
  Lemma inv_open' i P R : inv i P ∗ (P -∗ fupd M0 (P ∗ fupd M1 R)) ⊢ fupd M1 R.
  Proof.
    iIntros "(#HiP & HP)". iApply fupd_fupd. iApply inv_open; last first.
    { iSplit; first done. iExact "HP". }
    iIntros "(HP & HPw)". by iApply "HPw".
  Qed.

  Instance fupd_mono' E : Proper ((⊢) ==> (⊢)) (fupd E).
  Proof. intros P Q ?. by apply fupd_mono. Qed.
  Instance fupd_proper E : Proper ((⊣⊢) ==> (⊣⊢)) (fupd E).
  Proof.
    intros P Q; rewrite !uPred.equiv_spec=> -[??]; split; by apply fupd_mono.
  Qed.

  Lemma fupd_frame_r E P Q : fupd E P ∗ Q ⊢ fupd E (P ∗ Q).
  Proof. by rewrite comm fupd_frame_l comm. Qed.

  Global Instance elim_fupd_fupd E P Q : ElimModal (fupd E P) P (fupd E Q) (fupd E Q).
  Proof. by rewrite /ElimModal fupd_frame_r uPred.wand_elim_r fupd_fupd. Qed.

  Global Instance elim_fupd0_fupd1 P Q : ElimModal (fupd M0 P) P (fupd M1 Q) (fupd M1 Q).
  Proof.
    by rewrite /ElimModal fupd_frame_r uPred.wand_elim_r fupd_mask_mono fupd_fupd.
  Qed.

  Global Instance exists_split_fupd0 {A} E P (Φ : A → iProp) :
    FromExist P Φ → FromExist (fupd E P) (λ a, fupd E (Φ a)).
  Proof.
    rewrite /FromExist=>HP. apply uPred.exist_elim=> a.
    apply fupd_mono. by rewrite -HP -(uPred.exist_intro a).
  Qed.

  (** Now to the actual counterexample. We start with a weird form of saved propositions. *)
  Definition saved (γ : gname) (P : iProp) : iProp :=
    ∃ i, inv i (start γ ∨ (finished γ ∗ □ P)).
  Global Instance saved_persistent γ P : Persistent (saved γ P) := _.

  Lemma saved_alloc (P : gname → iProp) : fupd M1 (∃ γ, saved γ (P γ)).
  Proof.
    iIntros "". iMod (sts_alloc) as (γ) "Hs".
    iMod (inv_alloc (start γ ∨ (finished γ ∗ □ (P γ))) with "[Hs]") as (i) "#Hi".
    { auto. }
    iApply fupd_intro. by iExists γ, i.
  Qed.

  Lemma saved_cast γ P Q : saved γ P ∗ saved γ Q ∗ □ P ⊢ fupd M1 (□ Q).
  Proof.
    iIntros "(#HsP & #HsQ & #HP)". iDestruct "HsP" as (i) "HiP".
    iApply (inv_open' i). iSplit; first done.
    iIntros "HaP". iAssert (fupd M0 (finished γ)) with "[HaP]" as "> Hf".
    { iDestruct "HaP" as "[Hs | [Hf _]]".
      - by iApply start_finish.
      - by iApply fupd_intro. }
    iDestruct (finished_dup with "Hf") as "[Hf Hf']".
    iApply fupd_intro. iSplitL "Hf'"; first by eauto.
    (* Step 2: Open the Q-invariant. *)
    iClear (i) "HiP ". iDestruct "HsQ" as (i) "HiQ".
    iApply (inv_open' i). iSplit; first done.
    iIntros "[HaQ | [_ #HQ]]".
    { iExFalso. iApply finished_not_start. by iFrame. }
    iApply fupd_intro. iSplitL "Hf".
    { iRight. by iFrame. }
    by iApply fupd_intro.
  Qed.

  (** And now we tie a bad knot. *)
  Notation "¬ P" := (□ (P -∗ fupd M1 False))%I : uPred_scope.
  Definition A i : iProp := ∃ P, ¬P ∗ saved i P.
  Global Instance A_persistent i : Persistent (A i) := _.

  Lemma A_alloc : fupd M1 (∃ i, saved i (A i)).
  Proof. by apply saved_alloc. Qed.

  Lemma saved_NA i : saved i (A i) ⊢ ¬A i.
  Proof.
    iIntros "#Hi !# #HA". iPoseProof "HA" as "HA'".
    iDestruct "HA'" as (P) "#[HNP Hi']".
    iMod (saved_cast i (A i) P with "[]") as "HP".
    { eauto. }
    by iApply "HNP".
  Qed.

  Lemma saved_A i : saved i (A i) ⊢ A i.
  Proof.
    iIntros "#Hi". iExists (A i). iFrame "#".
    by iApply saved_NA.
  Qed.

  Lemma contradiction : False.
  Proof using All.
    apply consistency. iIntros "".
    iMod A_alloc as (i) "#H".
    iPoseProof (saved_NA with "H") as "HN".
    iApply "HN". iApply saved_A. done.
  Qed.
End inv. End inv.
