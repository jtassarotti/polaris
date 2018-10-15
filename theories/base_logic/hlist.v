From stdpp Require Export hlist.
From iris.base_logic Require Export base_logic.
Set Default Proof Using "Type".
Import uPred.

Fixpoint uPred_hexist {M As} : himpl As (uPred M) → uPred M :=
  match As return himpl As (uPred M) → uPred M with
  | tnil => id
  | tcons A As => λ Φ, ∃ x, uPred_hexist (Φ x)
  end%I.
Fixpoint uPred_hforall {M As} : himpl As (uPred M) → uPred M :=
  match As return himpl As (uPred M) → uPred M with
  | tnil => id
  | tcons A As => λ Φ, ∀ x, uPred_hforall (Φ x)
  end%I.

Section hlist.
Context {M : ucmraT}.

Lemma hexist_exist {As B} (f : himpl As B) (Φ : B → uPred M) :
  uPred_hexist (hcompose Φ f) ⊣⊢ ∃ xs : hlist As, Φ (f xs).
Proof.
  apply (anti_symm _).
  - induction As as [|A As IH]; simpl.
    + by rewrite -(exist_intro hnil) .
    + apply exist_elim=> x; rewrite IH; apply exist_elim=> xs.
      by rewrite -(exist_intro (hcons x xs)).
  - apply exist_elim=> xs; induction xs as [|A As x xs IH]; simpl; auto.
    by rewrite -(exist_intro x) IH.
Qed.

Lemma hforall_forall {As B} (f : himpl As B) (Φ : B → uPred M) :
  uPred_hforall (hcompose Φ f) ⊣⊢ ∀ xs : hlist As, Φ (f xs).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> xs; induction xs as [|A As x xs IH]; simpl; auto.
    by rewrite (forall_elim x) IH.
  - induction As as [|A As IH]; simpl.
    + by rewrite (forall_elim hnil) .
    + apply forall_intro=> x; rewrite -IH; apply forall_intro=> xs.
      by rewrite (forall_elim (hcons x xs)).
Qed.
End hlist.
