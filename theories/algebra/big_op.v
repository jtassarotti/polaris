From iris.algebra Require Export monoid.
From stdpp Require Export functions gmap gmultiset.
Set Default Proof Using "Type*".
Local Existing Instances monoid_ne monoid_assoc monoid_comm
  monoid_left_id monoid_right_id monoid_proper
  monoid_homomorphism_rel_po monoid_homomorphism_rel_proper
  monoid_homomorphism_op_proper
  monoid_homomorphism_ne weak_monoid_homomorphism_proper.

(** We define the following big operators with binders build in:

- The operator [ [^o list] k ↦ x ∈ l, P ] folds over a list [l]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o map] k ↦ x ∈ m, P ] folds over a map [m]. The binder [x]
  refers to each element at index [k].
- The operator [ [^o set] x ∈ X, P ] folds over a set [X]. The binder [x] refers
  to each element.

Since these big operators are like quantifiers, they have the same precedence as
[∀] and [∃]. *)

(** * Big ops over lists *)
Fixpoint big_opL `{Monoid M o} {A} (f : nat → A → M) (xs : list A) : M :=
  match xs with
  | [] => monoid_unit
  | x :: xs => o (f 0 x) (big_opL (λ n, f (S n)) xs)
  end.
Instance: Params (@big_opL) 4.
Arguments big_opL {M} o {_ A} _ !_ /.
Typeclasses Opaque big_opL.
Notation "'[^' o 'list]' k ↦ x ∈ l , P" := (big_opL o (λ k x, P) l)
  (at level 200, o at level 1, l at level 10, k, x at level 1, right associativity,
   format "[^ o  list]  k ↦ x  ∈  l ,  P") : stdpp_scope.
Notation "'[^' o 'list]' x ∈ l , P" := (big_opL o (λ _ x, P) l)
  (at level 200, o at level 1, l at level 10, x at level 1, right associativity,
   format "[^ o  list]  x  ∈  l ,  P") : stdpp_scope.

Definition big_opM `{Monoid M o} `{Countable K} {A} (f : K → A → M)
    (m : gmap K A) : M := big_opL o (λ _, curry f) (map_to_list m).
Instance: Params (@big_opM) 7.
Arguments big_opM {M} o {_ K _ _ A} _ _ : simpl never.
Typeclasses Opaque big_opM.
Notation "'[^' o 'map]' k ↦ x ∈ m , P" := (big_opM o (λ k x, P) m)
  (at level 200, o at level 1, m at level 10, k, x at level 1, right associativity,
   format "[^  o  map]  k ↦ x  ∈  m ,  P") : stdpp_scope.
Notation "'[^' o 'map]' x ∈ m , P" := (big_opM o (λ _ x, P) m)
  (at level 200, o at level 1, m at level 10, x at level 1, right associativity,
   format "[^ o  map]  x  ∈  m ,  P") : stdpp_scope.

Definition big_opS `{Monoid M o} `{Countable A} (f : A → M)
  (X : gset A) : M := big_opL o (λ _, f) (elements X).
Instance: Params (@big_opS) 6.
Arguments big_opS {M} o {_ A _ _} _ _ : simpl never.
Typeclasses Opaque big_opS.
Notation "'[^' o 'set]' x ∈ X , P" := (big_opS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  set]  x  ∈  X ,  P") : stdpp_scope.

Definition big_opMS `{Monoid M o} `{Countable A} (f : A → M)
  (X : gmultiset A) : M := big_opL o (λ _, f) (elements X).
Instance: Params (@big_opMS) 7.
Arguments big_opMS {M} o {_ A _ _} _ _ : simpl never.
Typeclasses Opaque big_opMS.
Notation "'[^' o 'mset]' x ∈ X , P" := (big_opMS o (λ x, P) X)
  (at level 200, o at level 1, X at level 10, x at level 1, right associativity,
   format "[^ o  mset]  x  ∈  X ,  P") : stdpp_scope.

(** * Properties about big ops *)
Section big_op.
Context `{Monoid M o}.
Implicit Types xs : list M.
Infix "`o`" := o (at level 50, left associativity).

(** ** Big ops over lists *)
Section list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types f g : nat → A → M.

  Lemma big_opL_nil f : ([^o list] k↦y ∈ [], f k y) = monoid_unit.
  Proof. done. Qed.
  Lemma big_opL_cons f x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (S k) y.
  Proof. done. Qed.
  Lemma big_opL_singleton f x : ([^o list] k↦y ∈ [x], f k y) ≡ f 0 x.
  Proof. by rewrite /= right_id. Qed.
  Lemma big_opL_app f l1 l2 :
    ([^o list] k↦y ∈ l1 ++ l2, f k y)
    ≡ ([^o list] k↦y ∈ l1, f k y) `o` ([^o list] k↦y ∈ l2, f (length l1 + k) y).
  Proof.
    revert f. induction l1 as [|x l1 IH]=> f /=; first by rewrite left_id.
    by rewrite IH assoc.
  Qed.

  Lemma big_opL_unit l : ([^o list] k↦y ∈ l, monoid_unit) ≡ (monoid_unit : M).
  Proof. induction l; rewrite /= ?left_id //. Qed.

  Lemma big_opL_forall R f g l :
    Reflexive R →
    Proper (R ==> R ==> R) o →
    (∀ k y, l !! k = Some y → R (f k y) (g k y)) →
    R ([^o list] k ↦ y ∈ l, f k y) ([^o list] k ↦ y ∈ l, g k y).
  Proof.
    intros ??. revert f g. induction l as [|x l IH]=> f g ? //=; f_equiv; eauto.
  Qed.

  Lemma big_opL_ext f g l :
    (∀ k y, l !! k = Some y → f k y = g k y) →
    ([^o list] k ↦ y ∈ l, f k y) = [^o list] k ↦ y ∈ l, g k y.
  Proof. apply big_opL_forall; apply _. Qed.
  Lemma big_opL_proper f g l :
    (∀ k y, l !! k = Some y → f k y ≡ g k y) →
    ([^o list] k ↦ y ∈ l, f k y) ≡ ([^o list] k ↦ y ∈ l, g k y).
  Proof. apply big_opL_forall; apply _. Qed.

  Lemma big_opL_permutation (f : A → M) l1 l2 :
    l1 ≡ₚ l2 → ([^o list] x ∈ l1, f x) ≡ ([^o list] x ∈ l2, f x).
  Proof.
    induction 1 as [|x xs1 xs2 ? IH|x y xs|xs1 xs2 xs3]; simpl; auto.
    - by rewrite IH.
    - by rewrite !assoc (comm _ (f x)).
    - by etrans.
  Qed.
  Global Instance big_opL_permutation' (f : A → M) :
    Proper ((≡ₚ) ==> (≡)) (big_opL o (λ _, f)).
  Proof. intros xs1 xs2. apply big_opL_permutation. Qed.

  Global Instance big_opL_ne n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==>
            eq ==> dist n) (big_opL o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opL_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_opL_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> eq ==> (≡))
           (big_opL o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opL_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_opL_consZ_l (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (1 + k)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.
  Lemma big_opL_consZ_r (f : Z → A → M) x l :
    ([^o list] k↦y ∈ x :: l, f k y) = f 0 x `o` [^o list] k↦y ∈ l, f (k + 1)%Z y.
  Proof. rewrite big_opL_cons. auto using big_opL_ext with f_equal lia. Qed.

  Lemma big_opL_fmap {B} (h : A → B) (f : nat → B → M) l :
    ([^o list] k↦y ∈ h <$> l, f k y) ≡ ([^o list] k↦y ∈ l, f k (h y)).
  Proof. revert f. induction l as [|x l IH]=> f; csimpl=> //. by rewrite IH. Qed.

  Lemma big_opL_opL f g l :
    ([^o list] k↦x ∈ l, f k x `o` g k x)
    ≡ ([^o list] k↦x ∈ l, f k x) `o` ([^o list] k↦x ∈ l, g k x).
  Proof.
    revert f g; induction l as [|x l IH]=> f g /=; first by rewrite left_id.
    by rewrite IH -!assoc (assoc _ (g _ _)) [(g _ _ `o` _)]comm -!assoc.
  Qed.
End list.

(** ** Big ops over finite maps *)
Section gmap.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types f g : K → A → M.

  Lemma big_opM_forall R f g m :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ k x, m !! k = Some x → R (f k x) (g k x)) →
    R ([^o map] k ↦ x ∈ m, f k x) ([^o map] k ↦ x ∈ m, g k x).
  Proof.
    intros ?? Hf. apply (big_opL_forall R); auto.
    intros k [i x] ?%elem_of_list_lookup_2. by apply Hf, elem_of_map_to_list.
  Qed.

  Lemma big_opM_ext f g m :
    (∀ k x, m !! k = Some x → f k x = g k x) →
    ([^o map] k ↦ x ∈ m, f k x) = ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_forall; apply _. Qed.
  Lemma big_opM_proper f g m :
    (∀ k x, m !! k = Some x → f k x ≡ g k x) →
    ([^o map] k ↦ x ∈ m, f k x) ≡ ([^o map] k ↦ x ∈ m, g k x).
  Proof. apply big_opM_forall; apply _. Qed.

  Global Instance big_opM_ne n :
    Proper (pointwise_relation _ (pointwise_relation _ (dist n)) ==> eq ==> dist n)
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_opM_proper' :
    Proper (pointwise_relation _ (pointwise_relation _ (≡)) ==> eq ==> (≡))
           (big_opM o (K:=K) (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opM_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_opM_empty f : ([^o map] k↦x ∈ ∅, f k x) = monoid_unit.
  Proof. by rewrite /big_opM map_to_list_empty. Qed.

  Lemma big_opM_insert f m i x :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, f k y) ≡ f i x `o` [^o map] k↦y ∈ m, f k y.
  Proof. intros ?. by rewrite /big_opM map_to_list_insert. Qed.

  Lemma big_opM_delete f m i x :
    m !! i = Some x →
    ([^o map] k↦y ∈ m, f k y) ≡ f i x `o` [^o map] k↦y ∈ delete i m, f k y.
  Proof.
    intros. rewrite -big_opM_insert ?lookup_delete //.
    by rewrite insert_delete insert_id.
  Qed.

  Lemma big_opM_singleton f i x : ([^o map] k↦y ∈ {[i:=x]}, f k y) ≡ f i x.
  Proof.
    rewrite -insert_empty big_opM_insert/=; last auto using lookup_empty.
    by rewrite big_opM_empty right_id.
  Qed.

  Lemma big_opM_unit m : ([^o map] k↦y ∈ m, monoid_unit) ≡ (monoid_unit : M).
  Proof. induction m using map_ind; rewrite /= ?big_opM_insert ?left_id //. Qed.

  Lemma big_opM_fmap {B} (h : A → B) (f : K → B → M) m :
    ([^o map] k↦y ∈ h <$> m, f k y) ≡ ([^o map] k↦y ∈ m, f k (h y)).
  Proof.
    rewrite /big_opM map_to_list_fmap big_opL_fmap.
    by apply big_opL_proper=> ? [??].
  Qed.

  Lemma big_opM_insert_override (f : K → A → M) m i x x' :
    m !! i = Some x → f i x ≡ f i x' →
    ([^o map] k↦y ∈ <[i:=x']> m, f k y) ≡ ([^o map] k↦y ∈ m, f k y).
  Proof.
    intros ? Hx. rewrite -insert_delete big_opM_insert ?lookup_delete //.
    by rewrite -Hx -big_opM_delete.
  Qed.

  Lemma big_opM_fn_insert {B} (g : K → A → B → M) (f : K → B) m i (x : A) b :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, g k y (<[i:=b]> f k))
    ≡ g i x b `o` [^o map] k↦y ∈ m, g k y (f k).
  Proof.
    intros. rewrite big_opM_insert // fn_lookup_insert.
    f_equiv; apply big_opM_proper; auto=> k y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opM_fn_insert' (f : K → M) m i x P :
    m !! i = None →
    ([^o map] k↦y ∈ <[i:=x]> m, <[i:=P]> f k) ≡ (P `o` [^o map] k↦y ∈ m, f k).
  Proof. apply (big_opM_fn_insert (λ _ _, id)). Qed.

  Lemma big_opM_opM f g m :
    ([^o map] k↦x ∈ m, f k x `o` g k x)
    ≡ ([^o map] k↦x ∈ m, f k x) `o` ([^o map] k↦x ∈ m, g k x).
  Proof. rewrite /big_opM -big_opL_opL. by apply big_opL_proper=> ? [??]. Qed.
End gmap.


(** ** Big ops over finite sets *)
Section gset.
  Context `{Countable A}.
  Implicit Types X : gset A.
  Implicit Types f : A → M.

  Lemma big_opS_forall R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o set] x ∈ X, f x) ([^o set] x ∈ X, g x).
  Proof.
    intros ?? Hf. apply (big_opL_forall R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, elem_of_elements.
  Qed.

  Lemma big_opS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o set] x ∈ X, f x) = ([^o set] x ∈ X, g x).
  Proof. apply big_opS_forall; apply _. Qed.
  Lemma big_opS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o set] x ∈ X, f x) ≡ ([^o set] x ∈ X, g x).
  Proof. apply big_opS_forall; apply _. Qed.

  Global Instance big_opS_ne n :
    Proper (pointwise_relation _ (dist n) ==> eq ==> dist n) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_opS_proper' :
    Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) (big_opS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opS_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_opS_empty f : ([^o set] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite /big_opS elements_empty. Qed.

  Lemma big_opS_insert f X x :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, f y) ≡ (f x `o` [^o set] y ∈ X, f y).
  Proof. intros. by rewrite /big_opS elements_union_singleton. Qed.
  Lemma big_opS_fn_insert {B} (f : A → B → M) h X x b :
    x ∉ X →
    ([^o set] y ∈ {[ x ]} ∪ X, f y (<[x:=b]> h y))
    ≡ f x b `o` [^o set] y ∈ X, f y (h y).
  Proof.
    intros. rewrite big_opS_insert // fn_lookup_insert.
    f_equiv; apply big_opS_proper; auto=> y ?.
    by rewrite fn_lookup_insert_ne; last set_solver.
  Qed.
  Lemma big_opS_fn_insert' f X x P :
    x ∉ X → ([^o set] y ∈ {[ x ]} ∪ X, <[x:=P]> f y) ≡ (P `o` [^o set] y ∈ X, f y).
  Proof. apply (big_opS_fn_insert (λ y, id)). Qed.

  Lemma big_opS_union f X Y :
    X ## Y →
    ([^o set] y ∈ X ∪ Y, f y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ Y, f y).
  Proof.
    intros. induction X as [|x X ? IH] using collection_ind_L.
    { by rewrite left_id_L big_opS_empty left_id. }
    rewrite -assoc_L !big_opS_insert; [|set_solver..].
    by rewrite -assoc IH; last set_solver.
  Qed.

  Lemma big_opS_delete f X x :
    x ∈ X → ([^o set] y ∈ X, f y) ≡ f x `o` [^o set] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opS_insert; last set_solver.
    by rewrite -union_difference_L; last set_solver.
  Qed.

  Lemma big_opS_singleton f x : ([^o set] y ∈ {[ x ]}, f y) ≡ f x.
  Proof. intros. by rewrite /big_opS elements_singleton /= right_id. Qed.

  Lemma big_opS_unit X : ([^o set] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    induction X using collection_ind_L; rewrite /= ?big_opS_insert ?left_id //.
  Qed.

  Lemma big_opS_opS f g X :
    ([^o set] y ∈ X, f y `o` g y) ≡ ([^o set] y ∈ X, f y) `o` ([^o set] y ∈ X, g y).
  Proof. by rewrite /big_opS -big_opL_opL. Qed.
End gset.

Lemma big_opM_dom `{Countable K} {A} (f : K → M) (m : gmap K A) :
  ([^o map] k↦_ ∈ m, f k) ≡ ([^o set] k ∈ dom _ m, f k).
Proof.
  induction m as [|i x ?? IH] using map_ind; [by rewrite dom_empty_L|].
  by rewrite dom_insert_L big_opM_insert // IH big_opS_insert ?not_elem_of_dom.
Qed.

(** ** Big ops over finite msets *)
Section gmultiset.
  Context `{Countable A}.
  Implicit Types X : gmultiset A.
  Implicit Types f : A → M.

  Lemma big_opMS_forall R f g X :
    Reflexive R → Proper (R ==> R ==> R) o →
    (∀ x, x ∈ X → R (f x) (g x)) →
    R ([^o mset] x ∈ X, f x) ([^o mset] x ∈ X, g x).
  Proof.
    intros ?? Hf. apply (big_opL_forall R); auto.
    intros k x ?%elem_of_list_lookup_2. by apply Hf, gmultiset_elem_of_elements.
  Qed.

  Lemma big_opMS_ext f g X :
    (∀ x, x ∈ X → f x = g x) →
    ([^o mset] x ∈ X, f x) = ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_forall; apply _. Qed.
  Lemma big_opMS_proper f g X :
    (∀ x, x ∈ X → f x ≡ g x) →
    ([^o mset] x ∈ X, f x) ≡ ([^o mset] x ∈ X, g x).
  Proof. apply big_opMS_forall; apply _. Qed.

  Global Instance big_opMS_ne n :
    Proper (pointwise_relation _ (dist n) ==> eq ==> dist n) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_forall; apply _ || intros; apply Hf. Qed.
  Global Instance big_opMS_proper' :
    Proper (pointwise_relation _ (≡) ==> eq ==> (≡)) (big_opMS o (A:=A)).
  Proof. intros f g Hf m ? <-. apply big_opMS_forall; apply _ || intros; apply Hf. Qed.

  Lemma big_opMS_empty f : ([^o mset] x ∈ ∅, f x) = monoid_unit.
  Proof. by rewrite /big_opMS gmultiset_elements_empty. Qed.

  Lemma big_opMS_union f X Y :
    ([^o mset] y ∈ X ∪ Y, f y) ≡ ([^o mset] y ∈ X, f y) `o` [^o mset] y ∈ Y, f y.
  Proof. by rewrite /big_opMS gmultiset_elements_union big_opL_app. Qed.

  Lemma big_opMS_singleton f x : ([^o mset] y ∈ {[ x ]}, f y) ≡ f x.
  Proof.
    intros. by rewrite /big_opMS gmultiset_elements_singleton /= right_id.
  Qed.

  Lemma big_opMS_delete f X x :
    x ∈ X → ([^o mset] y ∈ X, f y) ≡ f x `o` [^o mset] y ∈ X ∖ {[ x ]}, f y.
  Proof.
    intros. rewrite -big_opMS_singleton -big_opMS_union.
    by rewrite -gmultiset_union_difference'.
  Qed.

  Lemma big_opMS_unit X : ([^o mset] y ∈ X, monoid_unit) ≡ (monoid_unit : M).
  Proof.
    induction X using gmultiset_ind;
      rewrite /= ?big_opMS_union ?big_opMS_singleton ?left_id //.
  Qed.

  Lemma big_opMS_opMS f g X :
    ([^o mset] y ∈ X, f y `o` g y) ≡ ([^o mset] y ∈ X, f y) `o` ([^o mset] y ∈ X, g y).
  Proof. by rewrite /big_opMS -big_opL_opL. Qed.
End gmultiset.
End big_op.

Section homomorphisms.
  Context `{Monoid M1 o1, Monoid M2 o2}.
  Infix "`o1`" := o1 (at level 50, left associativity).
  Infix "`o2`" := o2 (at level 50, left associativity).
  Instance foo {A} (R : relation A) : RewriteRelation R.

  Lemma big_opL_commute {A} (h : M1 → M2) `{!MonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    revert f. induction l as [|x l IH]=> f /=.
    - apply monoid_homomorphism_unit.
    - by rewrite monoid_homomorphism IH.
  Qed.
  Lemma big_opL_commute1 {A} (h : M1 → M2) `{!WeakMonoidHomomorphism o1 o2 R h}
      (f : nat → A → M1) l :
    l ≠ [] → R (h ([^o1 list] k↦x ∈ l, f k x)) ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof.
    intros ?. revert f. induction l as [|x [|x' l'] IH]=> f //.
    - by rewrite !big_opL_singleton.
    - by rewrite !(big_opL_cons _ x) monoid_homomorphism IH.
  Qed.

  Lemma big_opM_commute `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind.
    - by rewrite !big_opM_empty monoid_homomorphism_unit.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opM_commute1 `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : K → A → M1) m :
    m ≠ ∅ → R (h ([^o1 map] k↦x ∈ m, f k x)) ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof.
    intros. induction m as [|i x m ? IH] using map_ind; [done|].
    destruct (decide (m = ∅)) as [->|].
    - by rewrite !big_opM_insert // !big_opM_empty !right_id.
    - by rewrite !big_opM_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using collection_ind_L.
    - by rewrite !big_opS_empty monoid_homomorphism_unit.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH.
  Qed.
  Lemma big_opS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X ? IH] using collection_ind_L; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opS_insert // !big_opS_empty !right_id.
    - by rewrite !big_opS_insert // monoid_homomorphism -IH //.
  Qed.

  Lemma big_opMS_commute `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind.
    - by rewrite !big_opMS_empty monoid_homomorphism_unit.
    - by rewrite !big_opMS_union !big_opMS_singleton monoid_homomorphism -IH.
  Qed.
  Lemma big_opMS_commute1 `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 R h} (f : A → M1) X :
    X ≠ ∅ → R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x)).
  Proof.
    intros. induction X as [|x X IH] using gmultiset_ind; [done|].
    destruct (decide (X = ∅)) as [->|].
    - by rewrite !big_opMS_union !big_opMS_singleton !big_opMS_empty !right_id.
    - by rewrite !big_opMS_union !big_opMS_singleton monoid_homomorphism -IH //.
  Qed.

  Context `{!LeibnizEquiv M2}.

  Lemma big_opL_commute_L {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof. unfold_leibniz. by apply big_opL_commute. Qed.
  Lemma big_opL_commute1_L {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : nat → A → M1) l :
    l ≠ [] → h ([^o1 list] k↦x ∈ l, f k x) = ([^o2 list] k↦x ∈ l, h (f k x)).
  Proof. unfold_leibniz. by apply big_opL_commute1. Qed.

  Lemma big_opM_commute_L `{Countable K} {A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof. unfold_leibniz. by apply big_opM_commute. Qed.
  Lemma big_opM_commute1_L `{Countable K} {A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : K → A → M1) m :
    m ≠ ∅ → h ([^o1 map] k↦x ∈ m, f k x) = ([^o2 map] k↦x ∈ m, h (f k x)).
  Proof. unfold_leibniz. by apply big_opM_commute1. Qed.

  Lemma big_opS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof. unfold_leibniz. by apply big_opS_commute. Qed.
  Lemma big_opS_commute1_L `{ Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 set] x ∈ X, f x) = ([^o2 set] x ∈ X, h (f x)).
  Proof. intros. rewrite <-leibniz_equiv_iff. by apply big_opS_commute1. Qed.

  Lemma big_opMS_commute_L `{Countable A} (h : M1 → M2)
      `{!MonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof. unfold_leibniz. by apply big_opMS_commute. Qed.
  Lemma big_opMS_commute1_L `{Countable A} (h : M1 → M2)
      `{!WeakMonoidHomomorphism o1 o2 (≡) h} (f : A → M1) X :
    X ≠ ∅ → h ([^o1 mset] x ∈ X, f x) = ([^o2 mset] x ∈ X, h (f x)).
  Proof. intros. rewrite <-leibniz_equiv_iff. by apply big_opMS_commute1. Qed.
End homomorphisms.
