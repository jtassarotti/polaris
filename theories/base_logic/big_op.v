From iris.algebra Require Export list big_op.
From iris.base_logic Require Export base_logic.
From stdpp Require Import gmap fin_collections gmultiset functions.
Set Default Proof Using "Type".
Import uPred.

(* Notations *)
Notation "'[∗' 'list]' k ↦ x ∈ l , P" := (big_opL uPred_sep (λ k x, P) l)
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∗  list]  k ↦ x  ∈  l ,  P") : uPred_scope.
Notation "'[∗' 'list]' x ∈ l , P" := (big_opL uPred_sep (λ _ x, P) l)
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∗  list]  x  ∈  l ,  P") : uPred_scope.

Notation "'[∗]' Ps" :=
  (big_opL uPred_sep (λ _ x, x) Ps) (at level 20) : uPred_scope.

Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM uPred_sep (λ k x, P) m)
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[∗  map]  k ↦ x  ∈  m ,  P") : uPred_scope.
Notation "'[∗' 'map]' x ∈ m , P" := (big_opM uPred_sep (λ _ x, P) m)
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[∗  map]  x  ∈  m ,  P") : uPred_scope.

Notation "'[∗' 'set]' x ∈ X , P" := (big_opS uPred_sep (λ x, P) X)
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  set]  x  ∈  X ,  P") : uPred_scope.

Notation "'[∗' 'mset]' x ∈ X , P" := (big_opMS uPred_sep (λ x, P) X)
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  mset]  x  ∈  X ,  P") : uPred_scope.

(** * Properties *)
Section big_op.
Context {M : ucmraT}.
Implicit Types Ps Qs : list (uPred M).
Implicit Types A : Type.

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → uPred M.

  Lemma big_sepL_nil Φ : ([∗ list] k↦y ∈ nil, Φ k y) ⊣⊢ True.
  Proof. done. Qed.
  Lemma big_sepL_nil' P Φ : P ⊢ [∗ list] k↦y ∈ nil, Φ k y.
  Proof. apply True_intro. Qed.
  Lemma big_sepL_cons Φ x l :
    ([∗ list] k↦y ∈ x :: l, Φ k y) ⊣⊢ Φ 0 x ∗ [∗ list] k↦y ∈ l, Φ (S k) y.
  Proof. by rewrite big_opL_cons. Qed.
  Lemma big_sepL_singleton Φ x : ([∗ list] k↦y ∈ [x], Φ k y) ⊣⊢ Φ 0 x.
  Proof. by rewrite big_opL_singleton. Qed.
  Lemma big_sepL_app Φ l1 l2 :
    ([∗ list] k↦y ∈ l1 ++ l2, Φ k y)
    ⊣⊢ ([∗ list] k↦y ∈ l1, Φ k y) ∗ ([∗ list] k↦y ∈ l2, Φ (length l1 + k) y).
  Proof. by rewrite big_opL_app. Qed.

  Lemma big_sepL_mono Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
  Proof. apply big_opL_forall; apply _. Qed.
  Lemma big_sepL_proper Φ Ψ l :
    (∀ k y, l !! k = Some y → Φ k y ⊣⊢ Ψ k y) →
    ([∗ list] k ↦ y ∈ l, Φ k y) ⊣⊢ ([∗ list] k ↦ y ∈ l, Ψ k y).
  Proof. apply big_opL_proper. Qed.
  Lemma big_sepL_submseteq (Φ : A → uPred M) l1 l2 :
    l1 ⊆+ l2 → ([∗ list] y ∈ l2, Φ y) ⊢ [∗ list] y ∈ l1, Φ y.
  Proof. intros [l ->]%submseteq_Permutation. by rewrite big_sepL_app sep_elim_l. Qed.

  Global Instance big_sepL_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opL (@uPred_sep M) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opL_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_sep_mono' :
    Proper (Forall2 (⊢) ==> (⊢)) (big_opL (@uPred_sep M) (λ _ P, P)).
  Proof. by induction 1 as [|P Q Ps Qs HPQ ? IH]; rewrite /= ?HPQ ?IH. Qed.

  Lemma big_sepL_lookup_acc Φ l i x :
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ list] k↦y ∈ l, Φ k y)).
  Proof.
    intros Hli. rewrite -(take_drop_middle l i x) // big_sepL_app /=.
    rewrite Nat.add_0_r take_length_le; eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepL_lookup Φ l i x :
    l !! i = Some x → ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x.
  Proof. intros. by rewrite big_sepL_lookup_acc // sep_elim_l. Qed.

  Lemma big_sepL_elem_of (Φ : A → uPred M) l x :
    x ∈ l → ([∗ list] y ∈ l, Φ y) ⊢ Φ x.
  Proof.
    intros [i ?]%elem_of_list_lookup; eauto using (big_sepL_lookup (λ _, Φ)).
  Qed.

  Lemma big_sepL_fmap {B} (f : A → B) (Φ : nat → B → uPred M) l :
    ([∗ list] k↦y ∈ f <$> l, Φ k y) ⊣⊢ ([∗ list] k↦y ∈ l, Φ k (f y)).
  Proof. by rewrite big_opL_fmap. Qed.

  Lemma big_sepL_sepL Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l, Φ k x) ∗ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. by rewrite big_opL_opL. Qed.

  Lemma big_sepL_and Φ Ψ l :
    ([∗ list] k↦x ∈ l, Φ k x ∧ Ψ k x)
    ⊢ ([∗ list] k↦x ∈ l, Φ k x) ∧ ([∗ list] k↦x ∈ l, Ψ k x).
  Proof. auto using big_sepL_mono with I. Qed.

  Lemma big_sepL_later Φ l :
    ▷ ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_laterN Φ n l :
    ▷^n ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, ▷^n Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_persistently Φ l :
    (□ [∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, □ Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_persistently_if p Φ l :
    □?p ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, □?p Φ k x).
  Proof. apply (big_opL_commute _). Qed.

  Lemma big_sepL_forall Φ l :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x).
  Proof.
    intros HΦ. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepL_lookup. }
    revert Φ HΦ. induction l as [|x l IH]=> Φ HΦ.
    { rewrite big_sepL_nil; auto with I. }
    rewrite big_sepL_cons. rewrite -and_sep_l; apply and_intro.
    - by rewrite (forall_elim 0) (forall_elim x) pure_True // True_impl.
    - rewrite -IH. apply forall_intro=> k; by rewrite (forall_elim (S k)).
  Qed.

  Lemma big_sepL_impl Φ Ψ l :
    □ (∀ k x, ⌜l !! k = Some x⌝ → Φ k x → Ψ k x) ∧ ([∗ list] k↦x ∈ l, Φ k x)
    ⊢ [∗ list] k↦x ∈ l, Ψ k x.
  Proof.
    rewrite persistently_and_sep_l. do 2 setoid_rewrite persistently_forall.
    setoid_rewrite persistently_impl; setoid_rewrite persistently_pure.
    rewrite -big_sepL_forall -big_sepL_sepL. apply big_sepL_mono; auto=> k x ?.
    by rewrite persistently_impl_wand persistently_elim wand_elim_l.
  Qed.

  Global Instance big_sepL_nil_plain Φ : Plain ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_plain Φ l :
    (∀ k x, Plain (Φ k x)) → Plain ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_plain_id Ps : TCForall Plain Ps → Plain ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_persistent Φ :
    Persistent ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_persistent Φ l :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_persistent_id Ps :
    TCForall Persistent Ps → Persistent ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.

  Global Instance big_sepL_nil_timeless Φ :
    Timeless ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_timeless Φ l :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.
  Global Instance big_sepL_timeless_id Ps :
    TCForall Timeless Ps → Timeless ([∗] Ps).
  Proof. induction 1; simpl; apply _. Qed.
End list.

Section list2.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → uPred M.
  (* Some lemmas depend on the generalized versions of the above ones. *)

  Lemma big_sepL_zip_with {B C} Φ f (l1 : list B) (l2 : list C) :
    ([∗ list] k↦x ∈ zip_with f l1 l2, Φ k x)
    ⊣⊢ ([∗ list] k↦x ∈ l1, ∀ y, ⌜l2 !! k = Some y⌝ → Φ k (f x y)).
  Proof.
    revert Φ l2; induction l1 as [|x l1 IH]=> Φ [|y l2] //.
    - apply (anti_symm _), True_intro.
      trans ([∗ list] _↦_ ∈ x :: l1, True : uPred M)%I.
      + rewrite big_sepL_forall. auto using forall_intro, impl_intro_l, True_intro.
      + apply big_sepL_mono=> k y _. apply forall_intro=> z.
        by apply impl_intro_l, pure_elim_l.
    - rewrite /= IH. apply sep_proper=> //. apply (anti_symm _).
      + apply forall_intro=>z /=. by apply impl_intro_r, pure_elim_r=>-[->].
      + rewrite (forall_elim y) /=. by eapply impl_elim, pure_intro.
  Qed.
End list2.

(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → uPred M.

  Lemma big_sepM_mono Φ Ψ m1 m2 :
    m2 ⊆ m1 → (∀ k x, m2 !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m1, Φ k x) ⊢ [∗ map] k ↦ x ∈ m2, Ψ k x.
  Proof.
    intros Hm HΦ. trans ([∗ map] k↦x ∈ m2, Φ k x)%I.
    - rewrite /big_opM. by apply big_sepL_submseteq, map_to_list_submseteq.
    - apply big_opM_forall; apply _ || auto.
  Qed.
  Lemma big_sepM_proper Φ Ψ m :
    (∀ k x, m !! k = Some x → Φ k x ⊣⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ ([∗ map] k ↦ x ∈ m, Ψ k x).
  Proof. apply big_opM_proper. Qed.

  Global Instance big_sepM_mono' :
    Proper (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (=) ==> (⊢))
           (big_opM (@uPred_sep M) (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepM_empty Φ : ([∗ map] k↦x ∈ ∅, Φ k x) ⊣⊢ True.
  Proof. by rewrite big_opM_empty. Qed.
  Lemma big_sepM_empty' P Φ : P ⊢ [∗ map] k↦x ∈ ∅, Φ k x.
  Proof. rewrite big_sepM_empty. apply True_intro. Qed.

  Lemma big_sepM_insert Φ m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepM_delete Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ Φ i x ∗ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. apply big_opM_delete. Qed.

  Lemma big_sepM_lookup_acc Φ m i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x ∗ (Φ i x -∗ ([∗ map] k↦y ∈ m, Φ k y)).
  Proof.
    intros. rewrite big_sepM_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepM_lookup Φ m i x :
    m !! i = Some x → ([∗ map] k↦y ∈ m, Φ k y) ⊢ Φ i x.
  Proof. intros. by rewrite big_sepM_lookup_acc // sep_elim_l. Qed.

  Lemma big_sepM_lookup_dom (Φ : K → uPred M) m i :
    is_Some (m !! i) → ([∗ map] k↦_ ∈ m, Φ k) ⊢ Φ i.
  Proof. intros [x ?]. by eapply (big_sepM_lookup (λ i x, Φ i)). Qed.

  Lemma big_sepM_singleton Φ i x : ([∗ map] k↦y ∈ {[i:=x]}, Φ k y) ⊣⊢ Φ i x.
  Proof. by rewrite big_opM_singleton. Qed.

  Lemma big_sepM_fmap {B} (f : A → B) (Φ : K → B → uPred M) m :
    ([∗ map] k↦y ∈ f <$> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (f y)).
  Proof. by rewrite big_opM_fmap. Qed.

  Lemma big_sepM_insert_override Φ m i x x' :
    m !! i = Some x → (Φ i x ⊣⊢ Φ i x') →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k y).
  Proof. apply big_opM_insert_override. Qed.

  Lemma big_sepM_insert_override_1 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y) ⊢
      (Φ i x' -∗ Φ i x) -∗ ([∗ map] k↦y ∈ m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
    by rewrite assoc wand_elim_l -big_sepM_delete.
  Qed.

  Lemma big_sepM_insert_override_2 Φ m i x x' :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) ⊢
      (Φ i x -∗ Φ i x') -∗ ([∗ map] k↦y ∈ <[i:=x']> m, Φ k y).
  Proof.
    intros ?. apply wand_intro_l.
    rewrite {1}big_sepM_delete //; rewrite assoc wand_elim_l.
    rewrite -insert_delete big_sepM_insert ?lookup_delete //.
  Qed.

  Lemma big_sepM_fn_insert {B} (Ψ : K → A → B → uPred M) (f : K → B) m i x b :
    m !! i = None →
       ([∗ map] k↦y ∈ <[i:=x]> m, Ψ k y (<[i:=b]> f k))
    ⊣⊢ (Ψ i x b ∗ [∗ map] k↦y ∈ m, Ψ k y (f k)).
  Proof. apply big_opM_fn_insert. Qed.

  Lemma big_sepM_fn_insert' (Φ : K → uPred M) m i x P :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, <[i:=P]> Φ k) ⊣⊢ (P ∗ [∗ map] k↦y ∈ m, Φ k).
  Proof. apply big_opM_fn_insert'. Qed.

  Lemma big_sepM_sepM Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∗ Ψ k x)
    ⊣⊢ ([∗ map] k↦x ∈ m, Φ k x) ∗ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. apply big_opM_opM. Qed.

  Lemma big_sepM_and Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x ∧ Ψ k x)
    ⊢ ([∗ map] k↦x ∈ m, Φ k x) ∧ ([∗ map] k↦x ∈ m, Ψ k x).
  Proof. auto using big_sepM_mono with I. Qed.

  Lemma big_sepM_later Φ m :
    ▷ ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_laterN Φ n m :
    ▷^n ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, ▷^n Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_persistently Φ m :
    (□ [∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, □ Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_persistently_if p Φ m :
    □?p ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, □?p Φ k x).
  Proof. apply (big_opM_commute _). Qed.

  Lemma big_sepM_forall Φ m :
    (∀ k x, Persistent (Φ k x)) →
    ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> k; apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepM_lookup. }
    induction m as [|i x m ? IH] using map_ind; auto using big_sepM_empty'.
    rewrite big_sepM_insert // -and_sep_l. apply and_intro.
    - rewrite (forall_elim i) (forall_elim x) lookup_insert.
      by rewrite pure_True // True_impl.
    - rewrite -IH. apply forall_mono=> k; apply forall_mono=> y.
      apply impl_intro_l, pure_elim_l=> ?.
      rewrite lookup_insert_ne; last by intros ?; simplify_map_eq.
      by rewrite pure_True // True_impl.
  Qed.

  Lemma big_sepM_impl Φ Ψ m :
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x → Ψ k x) ∧ ([∗ map] k↦x ∈ m, Φ k x)
    ⊢ [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    rewrite persistently_and_sep_l. do 2 setoid_rewrite persistently_forall.
    setoid_rewrite persistently_impl; setoid_rewrite persistently_pure.
    rewrite -big_sepM_forall -big_sepM_sepM. apply big_sepM_mono; auto=> k x ?.
    by rewrite persistently_impl_wand persistently_elim wand_elim_l.
  Qed.

  Global Instance big_sepM_empty_plain Φ : Plain ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_plain Φ m :
    (∀ k x, Plain (Φ k x)) → Plain ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sepL_plain=> _ [??]; apply _. Qed.

  Global Instance big_sepM_empty_persistent Φ :
    Persistent ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_persistent Φ m :
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sepL_persistent=> _ [??]; apply _. Qed.

  Global Instance big_sepM_nil_timeless Φ :
    Timeless ([∗ map] k↦x ∈ ∅, Φ k x).
  Proof. rewrite /big_opM map_to_list_empty. apply _. Qed.
  Global Instance big_sepM_timeless Φ m :
    (∀ k x, Timeless (Φ k x)) → Timeless ([∗ map] k↦x ∈ m, Φ k x).
  Proof. intros. apply big_sepL_timeless=> _ [??]; apply _. Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types Φ : A → uPred M.

  Lemma big_sepS_mono Φ Ψ X Y :
    Y ⊆ X → (∀ x, x ∈ Y → Φ x ⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ Y, Ψ x.
  Proof.
    intros HX HΦ. trans ([∗ set] x ∈ Y, Φ x)%I.
    - rewrite /big_opM. by apply big_sepL_submseteq, elements_submseteq.
    - apply big_opS_forall; apply _ || auto.
  Qed.
  Lemma big_sepS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ set] x ∈ X, Φ x) ⊣⊢ ([∗ set] x ∈ X, Ψ x).
  Proof. apply big_opS_proper. Qed.

  Global Instance big_sepS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opS (@uPred_sep M) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepS_empty Φ : ([∗ set] x ∈ ∅, Φ x) ⊣⊢ True.
  Proof. by rewrite big_opS_empty. Qed.
  Lemma big_sepS_empty' P Φ : P ⊢ [∗ set] x ∈ ∅, Φ x.
  Proof. rewrite big_sepS_empty. apply True_intro. Qed.

  Lemma big_sepS_insert Φ X x :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, Φ y) ⊣⊢ (Φ x ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_insert. Qed.

  Lemma big_sepS_fn_insert {B} (Ψ : A → B → uPred M) f X x b :
    x ∉ X →
       ([∗ set] y ∈ {[ x ]} ∪ X, Ψ y (<[x:=b]> f y))
    ⊣⊢ (Ψ x b ∗ [∗ set] y ∈ X, Ψ y (f y)).
  Proof. apply big_opS_fn_insert. Qed.

  Lemma big_sepS_fn_insert' Φ X x P :
    x ∉ X → ([∗ set] y ∈ {[ x ]} ∪ X, <[x:=P]> Φ y) ⊣⊢ (P ∗ [∗ set] y ∈ X, Φ y).
  Proof. apply big_opS_fn_insert'. Qed.

  Lemma big_sepS_union Φ X Y :
    X ## Y →
    ([∗ set] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ Y, Φ y).
  Proof. apply big_opS_union. Qed.

  Lemma big_sepS_delete Φ X x :
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ set] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opS_delete. Qed.

  Lemma big_sepS_elem_of Φ X x : x ∈ X → ([∗ set] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. rewrite big_sepS_delete //. auto with I. Qed.

  Lemma big_sepS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ set] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_singleton Φ x : ([∗ set] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opS_singleton. Qed.

  Lemma big_sepS_filter (P : A → Prop) `{∀ x, Decision (P x)} Φ X :
    ([∗ set] y ∈ filter P X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ⌜P y⌝ → Φ y).
  Proof.
    induction X as [|x X ? IH] using collection_ind_L.
    { by rewrite filter_empty_L !big_sepS_empty. }
    destruct (decide (P x)).
    - rewrite filter_union_L filter_singleton_L //.
      rewrite !big_sepS_insert //; last set_solver.
      by rewrite IH pure_True // left_id.
    - rewrite filter_union_L filter_singleton_not_L // left_id_L.
      by rewrite !big_sepS_insert // IH pure_False // False_impl left_id.
  Qed.

  Lemma big_sepS_filter_acc (P : A → Prop) `{∀ y, Decision (P y)} Φ X Y :
    (∀ y, y ∈ Y → P y → y ∈ X) →
    ([∗ set] y ∈ X, Φ y) -∗
      ([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) ∗
      (([∗ set] y ∈ Y, ⌜P y⌝ → Φ y) -∗ [∗ set] y ∈ X, Φ y).
  Proof.
    intros ?. destruct (proj1 (subseteq_disjoint_union_L (filter P Y) X))
      as (Z&->&?); first set_solver.
    rewrite big_sepS_union // big_sepS_filter. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepS_sepS Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ set] y ∈ X, Φ y) ∗ ([∗ set] y ∈ X, Ψ y).
  Proof. apply big_opS_opS. Qed.

  Lemma big_sepS_and Φ Ψ X :
    ([∗ set] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ set] y ∈ X, Φ y) ∧ ([∗ set] y ∈ X, Ψ y).
  Proof. auto using big_sepS_mono with I. Qed.

  Lemma big_sepS_later Φ X : ▷ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_laterN Φ n X :
    ▷^n ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_persistently Φ X : □ ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, □ Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_persistently_if q Φ X :
    □?q ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, □?q Φ y).
  Proof. apply (big_opS_commute _). Qed.

  Lemma big_sepS_forall Φ X :
    (∀ x, Persistent (Φ x)) → ([∗ set] x ∈ X, Φ x) ⊣⊢ (∀ x, ⌜x ∈ X⌝ → Φ x).
  Proof.
    intros. apply (anti_symm _).
    { apply forall_intro=> x.
      apply impl_intro_l, pure_elim_l=> ?; by apply big_sepS_elem_of. }
    induction X as [|x X ? IH] using collection_ind_L; auto using big_sepS_empty'.
    rewrite big_sepS_insert // -and_sep_l. apply and_intro.
    - by rewrite (forall_elim x) pure_True ?True_impl; last set_solver.
    - rewrite -IH. apply forall_mono=> y. apply impl_intro_l, pure_elim_l=> ?.
      by rewrite pure_True ?True_impl; last set_solver.
  Qed.

  Lemma big_sepS_impl Φ Ψ X :
    □ (∀ x, ⌜x ∈ X⌝ → Φ x → Ψ x) ∧ ([∗ set] x ∈ X, Φ x) ⊢ [∗ set] x ∈ X, Ψ x.
  Proof.
    rewrite persistently_and_sep_l persistently_forall.
    setoid_rewrite persistently_impl; setoid_rewrite persistently_pure.
    rewrite -big_sepS_forall -big_sepS_sepS. apply big_sepS_mono; auto=> x ?.
    by rewrite persistently_impl_wand persistently_elim wand_elim_l.
  Qed.

  Global Instance big_sepS_empty_plain Φ : Plain ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_plain Φ X :
    (∀ x, Plain (Φ x)) → Plain ([∗ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.

  Global Instance big_sepS_empty_persistent Φ : Persistent ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_persistent Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.

  Global Instance big_sepS_nil_timeless Φ : Timeless ([∗ set] x ∈ ∅, Φ x).
  Proof. rewrite /big_opS elements_empty. apply _. Qed.
  Global Instance big_sepS_timeless Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ set] x ∈ X, Φ x).
  Proof. rewrite /big_opS. apply _. Qed.
End gset.

Lemma big_sepM_dom `{Countable K} {A} (Φ : K → uPred M) (m : gmap K A) :
  ([∗ map] k↦_ ∈ m, Φ k) ⊣⊢ ([∗ set] k ∈ dom _ m, Φ k).
Proof. apply big_opM_dom. Qed.


(** ** Big ops over finite multisets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types Φ : A → uPred M.

  Lemma big_sepMS_mono Φ Ψ X Y :
    Y ⊆ X → (∀ x, x ∈ Y → Φ x ⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊢ [∗ mset] x ∈ Y, Ψ x.
  Proof.
    intros HX HΦ. trans ([∗ mset] x ∈ Y, Φ x)%I.
    - rewrite /big_opM. by apply big_sepL_submseteq, gmultiset_elements_submseteq.
    - apply big_opMS_forall; apply _ || auto.
  Qed.
  Lemma big_sepMS_proper Φ Ψ X :
    (∀ x, x ∈ X → Φ x ⊣⊢ Ψ x) →
    ([∗ mset] x ∈ X, Φ x) ⊣⊢ ([∗ mset] x ∈ X, Ψ x).
  Proof. apply big_opMS_proper. Qed.

  Global Instance big_sepMS_mono' :
     Proper (pointwise_relation _ (⊢) ==> (=) ==> (⊢)) (big_opMS (@uPred_sep M) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_sepMS_empty Φ : ([∗ mset] x ∈ ∅, Φ x) ⊣⊢ True.
  Proof. by rewrite big_opMS_empty. Qed.
  Lemma big_sepMS_empty' P Φ : P ⊢ [∗ mset] x ∈ ∅, Φ x.
  Proof. rewrite big_sepMS_empty. apply True_intro. Qed.

  Lemma big_sepMS_union Φ X Y :
    ([∗ mset] y ∈ X ∪ Y, Φ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ [∗ mset] y ∈ Y, Φ y.
  Proof. apply big_opMS_union. Qed.

  Lemma big_sepMS_delete Φ X x :
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ [∗ mset] y ∈ X ∖ {[ x ]}, Φ y.
  Proof. apply big_opMS_delete. Qed.

  Lemma big_sepMS_elem_of Φ X x : x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊢ Φ x.
  Proof. intros. by rewrite big_sepMS_delete // sep_elim_l. Qed.

  Lemma big_sepMS_elem_of_acc Φ X x :
    x ∈ X →
    ([∗ mset] y ∈ X, Φ y) ⊢ Φ x ∗ (Φ x -∗ ([∗ mset] y ∈ X, Φ y)).
  Proof.
    intros. rewrite big_sepMS_delete //. by apply sep_mono_r, wand_intro_l.
  Qed.

  Lemma big_sepMS_singleton Φ x : ([∗ mset] y ∈ {[ x ]}, Φ y) ⊣⊢ Φ x.
  Proof. apply big_opMS_singleton. Qed.

  Lemma big_sepMS_sepMS Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∗ Ψ y) ⊣⊢ ([∗ mset] y ∈ X, Φ y) ∗ ([∗ mset] y ∈ X, Ψ y).
  Proof. apply big_opMS_opMS. Qed.

  Lemma big_sepMS_and Φ Ψ X :
    ([∗ mset] y ∈ X, Φ y ∧ Ψ y) ⊢ ([∗ mset] y ∈ X, Φ y) ∧ ([∗ mset] y ∈ X, Ψ y).
  Proof. auto using big_sepMS_mono with I. Qed.

  Lemma big_sepMS_later Φ X : ▷ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷ Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_laterN Φ n X :
    ▷^n ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, ▷^n Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_persistently Φ X : □ ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, □ Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Lemma big_sepMS_persistently_if q Φ X :
    □?q ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, □?q Φ y).
  Proof. apply (big_opMS_commute _). Qed.

  Global Instance big_sepMS_empty_plain Φ : Plain ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite /big_opMS gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_plain Φ X :
    (∀ x, Plain (Φ x)) → Plain ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite /big_opMS. apply _. Qed.

  Global Instance big_sepMS_empty_persistent Φ : Persistent ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite /big_opMS gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_persistent Φ X :
    (∀ x, Persistent (Φ x)) → Persistent ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite /big_opMS. apply _. Qed.

  Global Instance big_sepMS_nil_timeless Φ : Timeless ([∗ mset] x ∈ ∅, Φ x).
  Proof. rewrite /big_opMS gmultiset_elements_empty. apply _. Qed.
  Global Instance big_sepMS_timeless Φ X :
    (∀ x, Timeless (Φ x)) → Timeless ([∗ mset] x ∈ X, Φ x).
  Proof. rewrite /big_opMS. apply _. Qed.
End gmultiset.
End big_op.
