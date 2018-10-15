From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Export auth.
From iris.algebra Require Import gmap.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* The CMRA we need. *)
Class authG Σ (A : ucmraT) := AuthG {
  auth_inG :> inG Σ (authR A);
  auth_cmra_discrete :> CmraDiscrete A;
}.
Definition authΣ (A : ucmraT) : gFunctors := #[ GFunctor (authR A) ].

Instance subG_authΣ Σ A : subG (authΣ A) Σ → CmraDiscrete A → authG Σ A.
Proof. solve_inG. Qed.

Section definitions.
  Context `{invG Σ, authG Σ A} {T : Type} (γ : gname).

  Definition auth_own (a : A) : iProp Σ :=
    own γ (◯ a).
  Definition auth_inv (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    (∃ t, own γ (● f t) ∗ φ t)%I.
  Definition auth_ctx (N : namespace) (f : T → A) (φ : T → iProp Σ) : iProp Σ :=
    inv N (auth_inv f φ).

  Global Instance auth_own_ne : NonExpansive auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_proper : Proper ((≡) ==> (⊣⊢)) auth_own.
  Proof. solve_proper. Qed.
  Global Instance auth_own_timeless a : Timeless (auth_own a).
  Proof. apply _. Qed.
  Global Instance auth_own_core_id a : CoreId a → Persistent (auth_own a).
  Proof. apply _. Qed.

  Global Instance auth_inv_ne n :
    Proper (pointwise_relation T (dist n) ==>
            pointwise_relation T (dist n) ==> dist n) auth_inv.
  Proof. solve_proper. Qed.
  Global Instance auth_inv_proper :
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (⊣⊢) ==> (⊣⊢)) auth_inv.
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_ne N n :
    Proper (pointwise_relation T (dist n) ==>
            pointwise_relation T (dist n) ==> dist n) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_proper N :
    Proper (pointwise_relation T (≡) ==>
            pointwise_relation T (⊣⊢) ==> (⊣⊢)) (auth_ctx N).
  Proof. solve_proper. Qed.
  Global Instance auth_ctx_persistent N f φ : Persistent (auth_ctx N f φ).
  Proof. apply _. Qed.
End definitions.

Typeclasses Opaque auth_own auth_inv auth_ctx.
Instance: Params (@auth_own) 4.
Instance: Params (@auth_inv) 5.
Instance: Params (@auth_ctx) 7.

Section auth.
  Context `{invG Σ, authG Σ A}.
  Context {T : Type} `{!Inhabited T}.
  Context (f : T → A) (φ : T → iProp Σ).
  Implicit Types N : namespace.
  Implicit Types P Q R : iProp Σ.
  Implicit Types a b : A.
  Implicit Types t u : T.
  Implicit Types γ : gname.

  Lemma auth_own_op γ a b : auth_own γ (a ⋅ b) ⊣⊢ auth_own γ a ∗ auth_own γ b.
  Proof. by rewrite /auth_own -own_op auth_frag_op. Qed.

  Global Instance from_and_auth_own γ a b1 b2 :
    IsOp a b1 b2 →
    FromAnd false (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 90.
  Proof. rewrite /IsOp /FromAnd=> ->. by rewrite auth_own_op. Qed.
  Global Instance from_and_auth_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → Or (CoreId b1) (CoreId b2) →
    FromAnd true (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 91.
  Proof.
    intros ? Hper; apply mk_from_and_persistent; [destruct Hper; apply _|].
    by rewrite -auth_own_op -is_op.
  Qed.

  Global Instance into_and_auth_own p γ a b1 b2 :
    IsOp a b1 b2 →
    IntoAnd p (auth_own γ a) (auth_own γ b1) (auth_own γ b2) | 90.
  Proof. intros. apply mk_into_and_sep. by rewrite (is_op a) auth_own_op. Qed.

  Lemma auth_own_mono γ a b : a ≼ b → auth_own γ b ⊢ auth_own γ a.
  Proof. intros [? ->]. by rewrite auth_own_op sep_elim_l. Qed.
  Lemma auth_own_valid γ a : auth_own γ a ⊢ ✓ a.
  Proof. by rewrite /auth_own own_valid auth_validI. Qed.
  Global Instance auth_own_sep_homomorphism γ :
    WeakMonoidHomomorphism op uPred_sep (≡) (auth_own γ).
  Proof. split; try apply _. apply auth_own_op. Qed.

  Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (auth_own γ).
  Proof. intros a1 a2. apply auth_own_mono. Qed.

  Lemma auth_alloc_strong N E t (G : gset gname) :
    ✓ (f t) → ▷ φ t ={E}=∗ ∃ γ, ⌜γ ∉ G⌝ ∧ auth_ctx γ N f φ ∧ auth_own γ (f t).
  Proof.
    iIntros (?) "Hφ". rewrite /auth_own /auth_ctx.
    iMod (own_alloc_strong (Auth (Excl' (f t)) (f t)) G) as (γ) "[% Hγ]"; first done.
    iRevert "Hγ"; rewrite auth_both_op; iIntros "[Hγ Hγ']".
    iMod (inv_alloc N _ (auth_inv γ f φ) with "[-Hγ']") as "#?".
    { iNext. rewrite /auth_inv. iExists t. by iFrame. }
    eauto.
  Qed.

  Lemma auth_alloc N E t :
    ✓ (f t) → ▷ φ t ={E}=∗ ∃ γ, auth_ctx γ N f φ ∧ auth_own γ (f t).
  Proof.
    iIntros (?) "Hφ".
    iMod (auth_alloc_strong N E t ∅ with "Hφ") as (γ) "[_ ?]"; eauto.
  Qed.

  Lemma auth_empty γ : (|==> auth_own γ ε)%I.
  Proof. by rewrite /auth_own -own_unit. Qed.

  Lemma auth_acc E γ a :
    ▷ auth_inv γ f φ ∗ auth_own γ a ={E}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E}=∗ ▷ auth_inv γ f φ ∗ auth_own γ b.
  Proof using Type*.
    iIntros "[Hinv Hγf]". rewrite /auth_inv /auth_own.
    iDestruct "Hinv" as (t) "[>Hγa Hφ]".
    iModIntro. iExists t.
    iDestruct (own_valid_2 with "Hγa Hγf") as % [? ?]%auth_valid_discrete_2.
    iSplit; first done. iFrame. iIntros (u b) "[% Hφ]".
    iMod (own_update_2 with "Hγa Hγf") as "[Hγa Hγf]".
    { eapply auth_update; eassumption. }
    iModIntro. iFrame. iExists u. iFrame.
  Qed.

  Lemma auth_open E N γ a :
    ↑N ⊆ E →
    auth_ctx γ N f φ ∗ auth_own γ a ={E,E∖↑N}=∗ ∃ t,
      ⌜a ≼ f t⌝ ∗ ▷ φ t ∗ ∀ u b,
      ⌜(f t, a) ~l~> (f u, b)⌝ ∗ ▷ φ u ={E∖↑N,E}=∗ auth_own γ b.
  Proof using Type*.
    iIntros (?) "[#? Hγf]". rewrite /auth_ctx. iInv N as "Hinv" "Hclose".
    (* The following is essentially a very trivial composition of the accessors
       [auth_acc] and [inv_open] -- but since we don't have any good support
       for that currently, this gets more tedious than it should, with us having
       to unpack and repack various proofs.
       TODO: Make this mostly automatic, by supporting "opening accessors
       around accessors". *)
    iMod (auth_acc with "[$Hinv $Hγf]") as (t) "(?&?&HclAuth)".
    iModIntro. iExists t. iFrame. iIntros (u b) "H".
    iMod ("HclAuth" $! u b with "H") as "(Hinv & ?)". by iMod ("Hclose" with "Hinv").
  Qed.
End auth.

Arguments auth_open {_ _ _} [_] {_} [_] _ _ _ _ _ _ _.
