From iris.algebra Require Export cmra.
Set Default Proof Using "Type".

(** * Frame preserving updates *)
(* This quantifies over [option A] for the frame.  That is necessary to
   make the following hold:
     x ~~> P → Some c ~~> Some P
*)
Definition cmra_updateP {A : cmraT} (x : A) (P : A → Prop) := ∀ n mz,
  ✓{n} (x ⋅? mz) → ∃ y, P y ∧ ✓{n} (y ⋅? mz).
Instance: Params (@cmra_updateP) 1.
Infix "~~>:" := cmra_updateP (at level 70).

Definition cmra_update {A : cmraT} (x y : A) := ∀ n mz,
  ✓{n} (x ⋅? mz) → ✓{n} (y ⋅? mz).
Infix "~~>" := cmra_update (at level 70).
Instance: Params (@cmra_update) 1.

Section updates.
Context {A : cmraT}.
Implicit Types x y : A.

Global Instance cmra_updateP_proper :
  Proper ((≡) ==> pointwise_relation _ iff ==> iff) (@cmra_updateP A).
Proof.
  rewrite /pointwise_relation /cmra_updateP=> x x' Hx P P' HP;
    split=> ? n mz; setoid_subst; naive_solver.
Qed.
Global Instance cmra_update_proper :
  Proper ((≡) ==> (≡) ==> iff) (@cmra_update A).
Proof.
  rewrite /cmra_update=> x x' Hx y y' Hy; split=> ? n mz ?; setoid_subst; auto.
Qed.

Lemma cmra_update_updateP x y : x ~~> y ↔ x ~~>: (y =).
Proof. split=> Hup n z ?; eauto. destruct (Hup n z) as (?&<-&?); auto. Qed.
Lemma cmra_updateP_id (P : A → Prop) x : P x → x ~~>: P.
Proof. intros ? n mz ?; eauto. Qed.
Lemma cmra_updateP_compose (P Q : A → Prop) x :
  x ~~>: P → (∀ y, P y → y ~~>: Q) → x ~~>: Q.
Proof. intros Hx Hy n mz ?. destruct (Hx n mz) as (y&?&?); naive_solver. Qed.
Lemma cmra_updateP_compose_l (Q : A → Prop) x y : x ~~> y → y ~~>: Q → x ~~>: Q.
Proof.
  rewrite cmra_update_updateP.
  intros; apply cmra_updateP_compose with (y =); naive_solver.
Qed.
Lemma cmra_updateP_weaken (P Q : A → Prop) x :
  x ~~>: P → (∀ y, P y → Q y) → x ~~>: Q.
Proof. eauto using cmra_updateP_compose, cmra_updateP_id. Qed.
Global Instance cmra_update_preorder : PreOrder (@cmra_update A).
Proof.
  split.
  - intros x. by apply cmra_update_updateP, cmra_updateP_id.
  - intros x y z. rewrite !cmra_update_updateP.
    eauto using cmra_updateP_compose with subst.
Qed.
Lemma cmra_update_exclusive `{!Exclusive x} y:
  ✓ y → x ~~> y.
Proof. move=>??[z|]=>[/exclusiveN_l[]|_]. by apply cmra_valid_validN. Qed.

Lemma cmra_updateP_op (P1 P2 Q : A → Prop) x1 x2 :
  x1 ~~>: P1 → x2 ~~>: P2 → (∀ y1 y2, P1 y1 → P2 y2 → Q (y1 ⋅ y2)) →
  x1 ⋅ x2 ~~>: Q.
Proof.
  intros Hx1 Hx2 Hy n mz ?.
  destruct (Hx1 n (Some (x2 ⋅? mz))) as (y1&?&?).
  { by rewrite /= -cmra_opM_assoc. }
  destruct (Hx2 n (Some (y1 ⋅? mz))) as (y2&?&?).
  { by rewrite /= -cmra_opM_assoc (comm _ x2) cmra_opM_assoc. }
  exists (y1 ⋅ y2); split; last rewrite (comm _ y1) cmra_opM_assoc; auto.
Qed.
Lemma cmra_updateP_op' (P1 P2 : A → Prop) x1 x2 :
  x1 ~~>: P1 → x2 ~~>: P2 →
  x1 ⋅ x2 ~~>: λ y, ∃ y1 y2, y = y1 ⋅ y2 ∧ P1 y1 ∧ P2 y2.
Proof. eauto 10 using cmra_updateP_op. Qed.
Lemma cmra_update_op x1 x2 y1 y2 : x1 ~~> y1 → x2 ~~> y2 → x1 ⋅ x2 ~~> y1 ⋅ y2.
Proof.
  rewrite !cmra_update_updateP; eauto using cmra_updateP_op with congruence.
Qed.

Lemma cmra_update_op_l x y : x ⋅ y ~~> x.
Proof. intros n mz. rewrite comm cmra_opM_assoc. apply cmra_validN_op_r. Qed.
Lemma cmra_update_op_r x y : x ⋅ y ~~> y.
Proof. rewrite comm. apply cmra_update_op_l. Qed.

Lemma cmra_update_valid0 x y : (✓{0} x → x ~~> y) → x ~~> y.
Proof.
  intros H n mz Hmz. apply H, Hmz.
  apply (cmra_validN_le n); last lia.
  destruct mz. eapply cmra_validN_op_l, Hmz. apply Hmz.
Qed.

(** ** Frame preserving updates for total CMRAs *)
Section total_updates.
  Local Set Default Proof Using "Type*".
  Context `{CmraTotal A}.

  Lemma cmra_total_updateP x (P : A → Prop) :
    x ~~>: P ↔ ∀ n z, ✓{n} (x ⋅ z) → ∃ y, P y ∧ ✓{n} (y ⋅ z).
  Proof.
    split=> Hup; [intros n z; apply (Hup n (Some z))|].
    intros n [z|] ?; simpl; [by apply Hup|].
    destruct (Hup n (core x)) as (y&?&?); first by rewrite cmra_core_r.
    eauto using cmra_validN_op_l.
  Qed.
  Lemma cmra_total_update x y : x ~~> y ↔ ∀ n z, ✓{n} (x ⋅ z) → ✓{n} (y ⋅ z).
  Proof. rewrite cmra_update_updateP cmra_total_updateP. naive_solver. Qed.

  Context `{CmraDiscrete A}.

  Lemma cmra_discrete_updateP (x : A) (P : A → Prop) :
    x ~~>: P ↔ ∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z).
  Proof.
    rewrite cmra_total_updateP; setoid_rewrite <-cmra_discrete_valid_iff.
    naive_solver eauto using 0.
  Qed.
  Lemma cmra_discrete_update (x y : A) :
    x ~~> y ↔ ∀ z, ✓ (x ⋅ z) → ✓ (y ⋅ z).
  Proof.
    rewrite cmra_total_update; setoid_rewrite <-cmra_discrete_valid_iff.
    naive_solver eauto using 0.
  Qed.
End total_updates.
End updates.

(** * Transport *)
Section cmra_transport.
  Context {A B : cmraT} (H : A = B).
  Notation T := (cmra_transport H).
  Lemma cmra_transport_updateP (P : A → Prop) (Q : B → Prop) x :
    x ~~>: P → (∀ y, P y → Q (T y)) → T x ~~>: Q.
  Proof. destruct H; eauto using cmra_updateP_weaken. Qed.
  Lemma cmra_transport_updateP' (P : A → Prop) x :
    x ~~>: P → T x ~~>: λ y, ∃ y', y = cmra_transport H y' ∧ P y'.
  Proof. eauto using cmra_transport_updateP. Qed.
End cmra_transport.

(** * Product *)
Section prod.
  Context {A B : cmraT}.
  Implicit Types x : A * B.

  Lemma prod_updateP P1 P2 (Q : A * B → Prop) x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → (∀ a b, P1 a → P2 b → Q (a,b)) → x ~~>: Q.
  Proof.
    intros Hx1 Hx2 HP n mz [??]; simpl in *.
    destruct (Hx1 n (fst <$> mz)) as (a&?&?); first by destruct mz.
    destruct (Hx2 n (snd <$> mz)) as (b&?&?); first by destruct mz.
    exists (a,b); repeat split; destruct mz; auto.
  Qed.
  Lemma prod_updateP' P1 P2 x :
    x.1 ~~>: P1 → x.2 ~~>: P2 → x ~~>: λ y, P1 (y.1) ∧ P2 (y.2).
  Proof. eauto using prod_updateP. Qed.
  Lemma prod_update x y : x.1 ~~> y.1 → x.2 ~~> y.2 → x ~~> y.
  Proof.
    rewrite !cmra_update_updateP.
    destruct x, y; eauto using prod_updateP with subst.
  Qed.
End prod.

(** * Option *)
Section option.
  Context {A : cmraT}.
  Implicit Types x y : A.

  Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
    x ~~>: P → (∀ y, P y → Q (Some y)) → Some x ~~>: Q.
  Proof.
    intros Hx Hy; apply cmra_total_updateP=> n [y|] ?.
    { destruct (Hx n (Some y)) as (y'&?&?); auto. exists (Some y'); auto. }
    destruct (Hx n None) as (y'&?&?); rewrite ?cmra_core_r; auto.
    by exists (Some y'); auto.
  Qed.
  Lemma option_updateP' (P : A → Prop) x :
    x ~~>: P → Some x ~~>: from_option P False.
  Proof. eauto using option_updateP. Qed.
  Lemma option_update x y : x ~~> y → Some x ~~> Some y.
  Proof. rewrite !cmra_update_updateP; eauto using option_updateP with subst. Qed.
End option.
