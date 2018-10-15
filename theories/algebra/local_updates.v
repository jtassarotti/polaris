From iris.algebra Require Export cmra.
Set Default Proof Using "Type".

(** * Local updates *)
Definition local_update {A : cmraT} (x y : A * A) := ∀ n mz,
  ✓{n} x.1 → x.1 ≡{n}≡ x.2 ⋅? mz → ✓{n} y.1 ∧ y.1 ≡{n}≡ y.2 ⋅? mz.
Instance: Params (@local_update) 1.
Infix "~l~>" := local_update (at level 70).

Section updates.
  Context {A : cmraT}.
  Implicit Types x y : A.

  Global Instance local_update_proper :
    Proper ((≡) ==> (≡) ==> iff) (@local_update A).
  Proof. unfold local_update. by repeat intro; setoid_subst. Qed.

  Global Instance local_update_preorder : PreOrder (@local_update A).
  Proof. split; unfold local_update; red; naive_solver. Qed.

  Lemma exclusive_local_update `{!Exclusive y} x x' : ✓ x' → (x,y) ~l~> (x',x').
  Proof.
    intros ? n mz Hxv Hx; simpl in *.
    move: Hxv; rewrite Hx; move=> /exclusiveN_opM=> ->; split; auto.
    by apply cmra_valid_validN.
  Qed.

  Lemma op_local_update x y z :
    (∀ n, ✓{n} x → ✓{n} (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros Hv n mz Hxv Hx; simpl in *; split; [by auto|].
    by rewrite Hx -cmra_opM_assoc.
  Qed.
  Lemma op_local_update_discrete `{!CmraDiscrete A} x y z :
    (✓ x → ✓ (z ⋅ x)) → (x,y) ~l~> (z ⋅ x, z ⋅ y).
  Proof.
    intros; apply op_local_update=> n. by rewrite -!(cmra_discrete_valid_iff n).
  Qed.

  Lemma op_local_update_frame x y x' y' yf :
    (x,y) ~l~> (x',y') → (x,y ⋅ yf) ~l~> (x', y' ⋅ yf).
  Proof.
    intros Hup n mz Hxv Hx; simpl in *.
    destruct (Hup n (Some (yf ⋅? mz))); [done|by rewrite /= -cmra_opM_assoc|].
    by rewrite cmra_opM_assoc.
  Qed.

  Lemma cancel_local_update x y z `{!Cancelable x} :
    (x ⋅ y, x ⋅ z) ~l~> (y, z).
  Proof.
    intros n f ? Heq. split; first by eapply cmra_validN_op_r.
    apply (cancelableN x); first done. by rewrite -cmra_opM_assoc.
  Qed.

  Lemma local_update_discrete `{!CmraDiscrete A} (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ mz, ✓ x → x ≡ y ⋅? mz → ✓ x' ∧ x' ≡ y' ⋅? mz.
  Proof.
    rewrite /local_update /=. setoid_rewrite <-cmra_discrete_valid_iff.
    setoid_rewrite <-(λ n, discrete_iff n x).
    setoid_rewrite <-(λ n, discrete_iff n x'). naive_solver eauto using 0.
  Qed.

  Lemma local_update_valid0 x y x' y' :
    (✓{0} x → ✓{0} y → x ≡{0}≡ y ∨ y ≼{0} x → (x,y) ~l~> (x',y')) →
    (x,y) ~l~> (x',y').
  Proof.
    intros Hup n mz Hmz Hz; simpl in *. apply Hup; auto.
    - by apply (cmra_validN_le n); last lia.
    - apply (cmra_validN_le n); last lia.
      move: Hmz; rewrite Hz. destruct mz; simpl; eauto using cmra_validN_op_l.
    - destruct mz as [z|].
      + right. exists z. apply dist_le with n; auto with lia.
      + left. apply dist_le with n; auto with lia.
  Qed.
  Lemma local_update_valid `{!CmraDiscrete A} x y x' y' :
    (✓ x → ✓ y → x ≡ y ∨ y ≼ x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    rewrite !(cmra_discrete_valid_iff 0)
      (cmra_discrete_included_iff 0) (discrete_iff 0).
    apply local_update_valid0.
  Qed.

  Lemma local_update_total_valid0 `{!CmraTotal A} x y x' y' :
    (✓{0} x → ✓{0} y → y ≼{0} x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    intros Hup. apply local_update_valid0=> ?? [Hx|?]; apply Hup; auto.
    by rewrite Hx.
  Qed.
  Lemma local_update_total_valid `{!CmraTotal A, !CmraDiscrete A} x y x' y' :
    (✓ x → ✓ y → y ≼ x → (x,y) ~l~> (x',y')) → (x,y) ~l~> (x',y').
  Proof.
    rewrite !(cmra_discrete_valid_iff 0) (cmra_discrete_included_iff 0).
    apply local_update_total_valid0.
  Qed.
End updates.

Section updates_unital.
  Context {A : ucmraT}.
  Implicit Types x y : A.

  Lemma local_update_unital x y x' y' :
    (x,y) ~l~> (x',y') ↔ ∀ n z,
      ✓{n} x → x ≡{n}≡ y ⋅ z → ✓{n} x' ∧ x' ≡{n}≡ y' ⋅ z.
  Proof.
    split.
    - intros Hup n z. apply (Hup _ (Some z)).
    - intros Hup n [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma local_update_unital_discrete `{!CmraDiscrete A} (x y x' y' : A) :
    (x,y) ~l~> (x',y') ↔ ∀ z, ✓ x → x ≡ y ⋅ z → ✓ x' ∧ x' ≡ y' ⋅ z.
  Proof.
    rewrite local_update_discrete. split.
    - intros Hup z. apply (Hup (Some z)).
    - intros Hup [z|]; simpl; [by auto|].
      rewrite -(right_id ε op y) -(right_id ε op y'). auto.
  Qed.

  Lemma cancel_local_update_unit x y `{!Cancelable x} :
    (x ⋅ y, x) ~l~> (y, ε).
  Proof. rewrite -{2}(right_id ε op x). by apply cancel_local_update. Qed.
End updates_unital.

(** * Product *)
Lemma prod_local_update {A B : cmraT} (x y x' y' : A * B) :
  (x.1,y.1) ~l~> (x'.1,y'.1) → (x.2,y.2) ~l~> (x'.2,y'.2) →
  (x,y) ~l~> (x',y').
Proof.
  intros Hup1 Hup2 n mz [??] [??]; simpl in *.
  destruct (Hup1 n (fst <$> mz)); [done|by destruct mz|].
  destruct (Hup2 n (snd <$> mz)); [done|by destruct mz|].
  by destruct mz.
Qed.

Lemma prod_local_update' {A B : cmraT} (x1 y1 x1' y1' : A) (x2 y2 x2' y2' : B) :
  (x1,y1) ~l~> (x1',y1') → (x2,y2) ~l~> (x2',y2') →
  ((x1,x2),(y1,y2)) ~l~> ((x1',x2'),(y1',y2')).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_1 {A B : cmraT} (x1 y1 x1' y1' : A) (x2 y2 : B) :
  (x1,y1) ~l~> (x1',y1') → ((x1,x2),(y1,y2)) ~l~> ((x1',x2),(y1',y2)).
Proof. intros. by apply prod_local_update. Qed.
Lemma prod_local_update_2 {A B : cmraT} (x1 y1 : A) (x2 y2 x2' y2' : B) :
  (x2,y2) ~l~> (x2',y2') → ((x1,x2),(y1,y2)) ~l~> ((x1,x2'),(y1,y2')).
Proof. intros. by apply prod_local_update. Qed.

(** * Option *)
(* TODO: Investigate whether we can use these in proving the very similar local
   updates on finmaps. *)
Lemma option_local_update {A : cmraT} (x y x' y' : A) :
  (x, y) ~l~> (x',y') →
  (Some x, Some y) ~l~> (Some x', Some y').
Proof.
  intros Hup. apply local_update_unital=>n mz Hxv Hx; simpl in *.
  destruct (Hup n mz); first done.
  { destruct mz as [?|]; inversion_clear Hx; auto. }
  split; first done. destruct mz as [?|]; constructor; auto.
Qed.

Lemma alloc_option_local_update {A : cmraT} (x : A) y :
  ✓ x →
  (None, y) ~l~> (Some x, Some x).
Proof.
  move=>Hx. apply local_update_unital=> n z _ /= Heq. split.
  { rewrite Some_validN. apply cmra_valid_validN. done. }
  destruct z as [z|]; last done. destruct y; inversion Heq.
Qed.

Lemma delete_option_local_update {A : cmraT} (x : option A) (y : A) :
  Exclusive y → (x, Some y) ~l~> (None, None).
Proof.
  move=>Hex. apply local_update_unital=>n z /= Hy Heq. split; first done.
  destruct z as [z|]; last done. exfalso.
  move: Hy. rewrite Heq /= -Some_op=>Hy. eapply Hex.
  eapply cmra_validN_le. eapply Hy. omega.
Qed.

(** * Natural numbers  *)
Lemma nat_local_update (x y x' y' : nat) :
  x + y' = x' + y → (x,y) ~l~> (x',y').
Proof.
  intros ??; apply local_update_unital_discrete=> z _.
  compute -[minus plus]; lia.
Qed.

Lemma mnat_local_update (x y x' : mnatUR) :
  x ≤ x' → (x,y) ~l~> (x',x').
Proof.
  intros ??; apply local_update_unital_discrete=> z _.
  compute -[max]; lia.
Qed.
