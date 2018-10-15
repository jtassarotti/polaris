From iris.proofmode Require Import base.
From iris.algebra Require Export base.
Set Default Proof Using "Type".

Inductive env (A : Type) : Type :=
  | Enil : env A
  | Esnoc : env A → ident → A → env A.
Arguments Enil {_}.
Arguments Esnoc {_} _ _ _.
Instance: Params (@Enil) 1.
Instance: Params (@Esnoc) 1.

Fixpoint env_lookup {A} (i : ident) (Γ : env A) : option A :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x => if ident_beq i j then Some x else env_lookup i Γ
  end.

Module env_notations.
  Notation "y ≫= f" := (option_bind f y).
  Notation "x ← y ; z" := (y ≫= λ x, z).
  Notation "' x1 .. xn ← y ; z" := (y ≫= (λ x1, .. (λ xn, z) .. )).
  Notation "Γ !! j" := (env_lookup j Γ).
End env_notations.
Import env_notations.

Inductive env_wf {A} : env A → Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf Γ i x : Γ !! i = None → env_wf Γ → env_wf (Esnoc Γ i x).

Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with Enil => [] | Esnoc Γ _ x => x :: env_to_list Γ end.
Coercion env_to_list : env >-> list.
Instance: Params (@env_to_list) 1.

Fixpoint env_dom {A} (Γ : env A) : list ident :=
  match Γ with Enil => [] | Esnoc Γ i _ => i :: env_dom Γ end.

Fixpoint env_app {A} (Γapp : env A) (Γ : env A) : option (env A) :=
  match Γapp with
  | Enil => Some Γ
  | Esnoc Γapp i x =>
     Γ' ← env_app Γapp Γ; 
     match Γ' !! i with None => Some (Esnoc Γ' i x) | Some _ => None end
  end.

Fixpoint env_replace {A} (i: ident) (Γi: env A) (Γ: env A) : option (env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if ident_beq i j then env_app Γi Γ else
     match Γi !! j with
     | None => Γ' ← env_replace i Γi Γ; Some (Esnoc Γ' j x)
     | Some _ => None
     end
  end.

Fixpoint env_delete {A} (i : ident) (Γ : env A) : env A :=
  match Γ with
  | Enil => Enil
  | Esnoc Γ j x => if ident_beq i j then Γ else Esnoc (env_delete i Γ) j x
  end.

Fixpoint env_lookup_delete {A} (i : ident) (Γ : env A) : option (A * env A) :=
  match Γ with
  | Enil => None
  | Esnoc Γ j x =>
     if ident_beq i j then Some (x,Γ)
     else ''(y,Γ') ← env_lookup_delete i Γ; Some (y, Esnoc Γ' j x)
  end.

Inductive env_Forall2 {A B} (P : A → B → Prop) : env A → env B → Prop :=
  | env_Forall2_nil : env_Forall2 P Enil Enil
  | env_Forall2_snoc Γ1 Γ2 i x y :
     env_Forall2 P Γ1 Γ2 → P x y → env_Forall2 P (Esnoc Γ1 i x) (Esnoc Γ2 i y).

Inductive env_subenv {A} : relation (env A) :=
  | env_subenv_nil : env_subenv Enil Enil
  | env_subenv_snoc Γ1 Γ2 i x :
     env_subenv Γ1 Γ2 → env_subenv (Esnoc Γ1 i x) (Esnoc Γ2 i x)
  | env_subenv_skip Γ1 Γ2 i y :
     env_subenv Γ1 Γ2 → env_subenv Γ1 (Esnoc Γ2 i y).

Section env.
Context {A : Type}.
Implicit Types Γ : env A.
Implicit Types i : ident.
Implicit Types x : A.
Hint Resolve Esnoc_wf Enil_wf.

Ltac simplify :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H : context [ident_beq ?s1 ?s2] |- _ => destruct (ident_beq_reflect s1 s2)
  | |- context [ident_beq ?s1 ?s2] => destruct (ident_beq_reflect s1 s2)
  | H : context [option_bind _ ?x] |- _ => destruct x eqn:?
  | |- context [option_bind _ ?x] => destruct x eqn:?
  | _ => case_match
  end.

Lemma env_lookup_perm Γ i x : Γ !! i = Some x → Γ ≡ₚ x :: env_delete i Γ.
Proof.
  induction Γ; intros; simplify; rewrite 1?Permutation_swap; f_equiv; eauto.
Qed.

Lemma env_lookup_snoc Γ i P : env_lookup i (Esnoc Γ i P) = Some P.
Proof. induction Γ; simplify; auto. Qed.
Lemma env_lookup_snoc_ne Γ i j P :
  i ≠ j → env_lookup i (Esnoc Γ j P) = env_lookup i Γ.
Proof. induction Γ=> ?; simplify; auto. Qed.

Lemma env_app_perm Γ Γapp Γ' :
  env_app Γapp Γ = Some Γ' → env_to_list Γ' ≡ₚ Γapp ++ Γ.
Proof. revert Γ'; induction Γapp; intros; simplify; f_equal; auto. Qed.
Lemma env_app_fresh Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None → Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_fresh_1 Γ Γapp Γ' i x :
  env_app Γapp Γ = Some Γ' → Γ' !! i = None → Γ !! i = None.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.
Lemma env_app_disjoint Γ Γapp Γ' i :
  env_app Γapp Γ = Some Γ' → Γapp !! i = None ∨ Γ !! i = None.
Proof.
  revert Γ'.
  induction Γapp; intros; simplify; naive_solver eauto using env_app_fresh_1.
Qed.
Lemma env_app_wf Γ Γapp Γ' : env_app Γapp Γ = Some Γ' → env_wf Γ → env_wf Γ'.
Proof. revert Γ'. induction Γapp; intros; simplify; eauto. Qed.

Lemma env_replace_fresh Γ Γj Γ' i j :
  env_replace j Γj Γ = Some Γ' →
  Γj !! i = None → env_delete j Γ !! i = None → Γ' !! i = None.
Proof. revert Γ'. induction Γ; intros; simplify; eauto using env_app_fresh. Qed.
Lemma env_replace_wf Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → env_wf (env_delete i Γ) → env_wf Γ'.
Proof.
  revert Γ'. induction Γ; intros ??; simplify; [|inversion_clear 1];
    eauto using env_app_wf, env_replace_fresh.
Qed.
Lemma env_replace_lookup Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → is_Some (Γ !! i).
Proof. revert Γ'. induction Γ; intros; simplify; eauto. Qed.
Lemma env_replace_perm Γ Γi Γ' i :
  env_replace i Γi Γ = Some Γ' → Γ' ≡ₚ Γi ++ env_delete i Γ.
Proof.
  revert Γ'. induction Γ as [|Γ IH j y]=>Γ' ?; simplify; auto using env_app_perm.
  rewrite -Permutation_middle -IH //.
Qed.

Lemma env_lookup_delete_correct Γ i :
  env_lookup_delete i Γ = (x ← Γ !! i; Some (x,env_delete i Γ)).
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_lookup_delete_Some Γ Γ' i x :
  env_lookup_delete i Γ = Some (x,Γ') ↔ Γ !! i = Some x ∧ Γ' = env_delete i Γ.
Proof. rewrite env_lookup_delete_correct; simplify; naive_solver. Qed.

Lemma env_lookup_env_delete Γ j : env_wf Γ → env_delete j Γ !! j = None.
Proof. induction 1; intros; simplify; eauto. Qed.
Lemma env_lookup_env_delete_ne Γ i j : i ≠ j → env_delete j Γ !! i = Γ !! i.
Proof. induction Γ; intros; simplify; eauto. Qed.
Lemma env_delete_fresh Γ i j : Γ !! i = None → env_delete j Γ !! i = None.
Proof. induction Γ; intros; simplify; eauto. Qed.

Lemma env_delete_wf Γ j : env_wf Γ → env_wf (env_delete j Γ).
Proof. induction 1; simplify; eauto using env_delete_fresh. Qed.

Global Instance env_Forall2_refl (P : relation A) :
  Reflexive P → Reflexive (env_Forall2 P).
Proof. intros ? Γ. induction Γ; constructor; auto. Qed.
Global Instance env_Forall2_sym (P : relation A) :
  Symmetric P → Symmetric (env_Forall2 P).
Proof. induction 2; constructor; auto. Qed.
Global Instance env_Forall2_trans (P : relation A) :
  Transitive P → Transitive (env_Forall2 P).
Proof.
  intros ? Γ1 Γ2 Γ3 HΓ; revert Γ3.
  induction HΓ; inversion_clear 1; constructor; eauto.
Qed.
Global Instance env_Forall2_antisymm (P Q : relation A) :
  AntiSymm P Q → AntiSymm (env_Forall2 P) (env_Forall2 Q).
Proof. induction 2; inversion_clear 1; constructor; auto. Qed.
Lemma env_Forall2_impl {B} (P Q : A → B → Prop) Γ Σ :
  env_Forall2 P Γ Σ → (∀ x y, P x y → Q x y) → env_Forall2 Q Γ Σ.
Proof. induction 1; constructor; eauto. Qed.

Global Instance Esnoc_proper (P : relation A) :
  Proper (env_Forall2 P ==> (=) ==> P ==> env_Forall2 P) Esnoc.
Proof. intros Γ1 Γ2 HΓ i ? <-; by constructor. Qed.
Global Instance env_to_list_proper (P : relation A) :
  Proper (env_Forall2 P ==> Forall2 P) env_to_list.
Proof. induction 1; constructor; auto. Qed.

Lemma env_Forall2_fresh {B} (P : A → B → Prop) Γ Σ i :
  env_Forall2 P Γ Σ → Γ !! i = None → Σ !! i = None.
Proof. by induction 1; simplify. Qed.
Lemma env_Forall2_wf {B} (P : A → B → Prop) Γ Σ :
  env_Forall2 P Γ Σ → env_wf Γ → env_wf Σ.
Proof. induction 1; inversion_clear 1; eauto using env_Forall2_fresh. Qed.

Lemma env_subenv_fresh Γ Σ i : env_subenv Γ Σ → Σ !! i = None → Γ !! i = None.
Proof. by induction 1; simplify. Qed.
Lemma env_subenv_wf Γ Σ : env_subenv Γ Σ → env_wf Σ → env_wf Γ.
Proof. induction 1; inversion_clear 1; eauto using env_subenv_fresh. Qed.
Global Instance env_to_list_subenv_proper :
  Proper (env_subenv ==> sublist) (@env_to_list A).
Proof. induction 1; simpl; constructor; auto. Qed.
End env.
