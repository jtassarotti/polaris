From iris.algebra Require Import functions gmap.
From iris.base_logic Require Import big_op.
From iris.base_logic Require Export iprop.
From iris.proofmode Require Import classes.
Set Default Proof Using "Type".
Import uPred.

(** The class [inG Σ A] expresses that the CMRA [A] is in the list of functors
[Σ]. This class is similar to the [subG] class, but written down in terms of
individual CMRAs instead of (lists of) CMRA *functors*. This additional class is
needed because Coq is otherwise unable to solve type class constraints due to
higher-order unification problems. *)
Class inG (Σ : gFunctors) (A : cmraT) :=
  InG { inG_id : gid Σ; inG_prf : A = Σ inG_id (iPreProp Σ) }.
Arguments inG_id {_ _} _.

Lemma subG_inG Σ (F : gFunctor) : subG F Σ → inG Σ (F (iPreProp Σ)).
Proof. move=> /(_ 0%fin) /= [j ->]. by exists j. Qed.

(** This tactic solves the usual obligations "subG ? Σ → {in,?}G ? Σ" *)
Ltac solve_inG :=
  (* Get all assumptions *)
  intros;
  (* Unfold the top-level xΣ. We need to support this to be a function. *)
  lazymatch goal with
  | H : subG (?xΣ _ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _ _) _ |- _ => try unfold xΣ in H
  | H : subG (?xΣ _) _ |- _ => try unfold xΣ in H
  | H : subG ?xΣ _ |- _ => try unfold xΣ in H
  end;
  (* Take apart subG for non-"atomic" lists *)
  repeat match goal with
         | H : subG (gFunctors.app _ _) _ |- _ => apply subG_inv in H; destruct H
         end;
  (* Try to turn singleton subG into inG; but also keep the subG for typeclass
     resolution -- to keep them, we put them onto the goal. *)
  repeat match goal with
         | H : subG _ _ |- _ => move:(H); (apply subG_inG in H || clear H)
         end;
  (* Again get all assumptions *)
  intros;
  (* We support two kinds of goals: Things convertible to inG;
     and records with inG and typeclass fields. Try to solve the
     first case. *)
  try done;
  (* That didn't work, now we're in for the second case. *)
  split; (assumption || by apply _).

(** * Definition of the connective [own] *)
Definition iRes_singleton `{i : inG Σ A} (γ : gname) (a : A) : iResUR Σ :=
  ofe_fun_singleton (inG_id i) {[ γ := cmra_transport inG_prf a ]}.
Instance: Params (@iRes_singleton) 4.

Definition own_def `{inG Σ A} (γ : gname) (a : A) : iProp Σ :=
  uPred_ownM (iRes_singleton γ a).
Definition own_aux : seal (@own_def). by eexists. Qed.
Definition own {Σ A i} := unseal own_aux Σ A i.
Definition own_eq : @own = @own_def := seal_eq own_aux.
Instance: Params (@own) 4.
Typeclasses Opaque own.

(** * Properties about ghost ownership *)
Section global.
Context `{inG Σ A}.
Implicit Types a : A.

(** ** Properties of [iRes_singleton] *)
Global Instance iRes_singleton_ne γ :
  NonExpansive (@iRes_singleton Σ A _ γ).
Proof. by intros n a a' Ha; apply ofe_fun_singleton_ne; rewrite Ha. Qed.
Lemma iRes_singleton_op γ a1 a2 :
  iRes_singleton γ (a1 ⋅ a2) ≡ iRes_singleton γ a1 ⋅ iRes_singleton γ a2.
Proof.
  by rewrite /iRes_singleton ofe_fun_op_singleton op_singleton cmra_transport_op.
Qed.

(** ** Properties of [own] *)
Global Instance own_ne γ : NonExpansive (@own Σ A _ γ).
Proof. rewrite !own_eq. solve_proper. Qed.
Global Instance own_proper γ :
  Proper ((≡) ==> (⊣⊢)) (@own Σ A _ γ) := ne_proper _.

Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) ⊣⊢ own γ a1 ∗ own γ a2.
Proof. by rewrite !own_eq /own_def -ownM_op iRes_singleton_op. Qed.
Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 ⊢ own γ a2.
Proof. move=> [c ->]. rewrite own_op. eauto with I. Qed.

Global Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own Σ A _ γ).
Proof. intros a1 a2. apply own_mono. Qed.

Lemma own_valid γ a : own γ a ⊢ ✓ a.
Proof.
  rewrite !own_eq /own_def ownM_valid /iRes_singleton.
  rewrite ofe_fun_validI (forall_elim (inG_id _)) ofe_fun_lookup_singleton.
  rewrite gmap_validI (forall_elim γ) lookup_singleton option_validI.
  (* implicit arguments differ a bit *)
  by trans (✓ cmra_transport inG_prf a : iProp Σ)%I; last destruct inG_prf.
Qed.
Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
Proof. apply wand_intro_r. by rewrite -own_op own_valid. Qed.
Lemma own_valid_3 γ a1 a2 a3 : own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
Proof. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
Proof. apply: uPred.sep_entails_r. apply own_valid. Qed.
Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
Proof. by rewrite comm -own_valid_r. Qed.

Global Instance own_timeless γ a : Discrete a → Timeless (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.
Global Instance own_core_persistent γ a : CoreId a → Persistent (own γ a).
Proof. rewrite !own_eq /own_def; apply _. Qed.

(** ** Allocation *)
(* TODO: This also holds if we just have ✓ a at the current step-idx, as Iris
   assertion. However, the map_updateP_alloc does not suffice to show this. *)
Lemma own_alloc_strong a (G : gset gname) :
  ✓ a → (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ own γ a)%I.
Proof.
  intros Ha.
  rewrite -(bupd_mono (∃ m, ⌜∃ γ, γ ∉ G ∧ m = iRes_singleton γ a⌝ ∧ uPred_ownM m)%I).
  - rewrite /uPred_valid ownM_unit.
    eapply bupd_ownM_updateP, (ofe_fun_singleton_updateP_empty (inG_id _));
      first (eapply alloc_updateP_strong', cmra_transport_valid, Ha);
      naive_solver.
  - apply exist_elim=>m; apply pure_elim_l=>-[γ [Hfresh ->]].
    by rewrite !own_eq /own_def -(exist_intro γ) pure_True // left_id.
Qed.
Lemma own_alloc a : ✓ a → (|==> ∃ γ, own γ a)%I.
Proof.
  intros Ha. rewrite /uPred_valid (own_alloc_strong a ∅) //; [].
  apply bupd_mono, exist_mono=>?. eauto with I.
Qed.

(** ** Frame preserving updates *)
Lemma own_updateP P γ a : a ~~>: P → own γ a ==∗ ∃ a', ⌜P a'⌝ ∧ own γ a'.
Proof.
  intros Ha. rewrite !own_eq.
  rewrite -(bupd_mono (∃ m, ⌜∃ a', m = iRes_singleton γ a' ∧ P a'⌝ ∧ uPred_ownM m)%I).
  - eapply bupd_ownM_updateP, ofe_fun_singleton_updateP;
      first by (eapply singleton_updateP', cmra_transport_updateP', Ha).
    naive_solver.
  - apply exist_elim=>m; apply pure_elim_l=>-[a' [-> HP]].
    rewrite -(exist_intro a'). by apply and_intro; [apply pure_intro|].
Qed.

Lemma own_update γ a a' : a ~~> a' → own γ a ==∗ own γ a'.
Proof.
  intros; rewrite (own_updateP (a' =)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> a''; apply pure_elim_l=> ->.
Qed.
Lemma own_update_2 γ a1 a2 a' :
  a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
Proof. intros. apply wand_intro_r. rewrite -own_op. by apply own_update. Qed.
Lemma own_update_3 γ a1 a2 a3 a' :
  a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
Proof. intros. do 2 apply wand_intro_r. rewrite -!own_op. by apply own_update. Qed.
End global.

Arguments own_valid {_ _} [_] _ _.
Arguments own_valid_2 {_ _} [_] _ _ _.
Arguments own_valid_3 {_ _} [_] _ _ _ _.
Arguments own_valid_l {_ _} [_] _ _.
Arguments own_valid_r {_ _} [_] _ _.
Arguments own_updateP {_ _} [_] _ _ _ _.
Arguments own_update {_ _} [_] _ _ _ _.
Arguments own_update_2 {_ _} [_] _ _ _ _ _.
Arguments own_update_3 {_ _} [_] _ _ _ _ _ _.

Lemma own_unit A `{inG Σ (A:ucmraT)} γ : (|==> own γ ε)%I.
Proof.
  rewrite /uPred_valid ownM_unit !own_eq /own_def.
  apply bupd_ownM_update, ofe_fun_singleton_update_empty.
  apply (alloc_unit_singleton_update (cmra_transport inG_prf ε)); last done.
  - apply cmra_transport_valid, ucmra_unit_valid.
  - intros x; destruct inG_prf. by rewrite left_id.
Qed.

(** Big op class instances *)
Instance own_cmra_sep_homomorphism `{inG Σ (A:ucmraT)} :
  WeakMonoidHomomorphism op uPred_sep (≡) (own γ).
Proof. split; try apply _. apply own_op. Qed.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{inG Σ A}.
  Implicit Types a b : A.

  Global Instance into_and_own p γ a b1 b2 :
    IsOp a b1 b2 → IntoAnd p (own γ a) (own γ b1) (own γ b2).
  Proof. intros. apply mk_into_and_sep. by rewrite (is_op a) own_op. Qed.
  Global Instance from_and_own γ a b1 b2 :
    IsOp a b1 b2 → FromAnd false (own γ a) (own γ b1) (own γ b2).
  Proof. intros. by rewrite /FromAnd -own_op -is_op. Qed.
  Global Instance from_and_own_persistent γ a b1 b2 :
    IsOp a b1 b2 → Or (CoreId b1) (CoreId b2) →
    FromAnd true (own γ a) (own γ b1) (own γ b2).
  Proof.
    intros ? Hper; apply mk_from_and_persistent; [destruct Hper; apply _|].
    by rewrite -own_op -is_op.
  Qed.
End proofmode_classes.
