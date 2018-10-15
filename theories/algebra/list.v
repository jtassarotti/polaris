From iris.algebra Require Export cmra.
From stdpp Require Export list.
From iris.base_logic Require Import base_logic.
From iris.algebra Require Import updates local_updates.
Set Default Proof Using "Type".

Section cofe.
Context {A : ofeT}.
Implicit Types l : list A.

Instance list_dist : Dist (list A) := λ n, Forall2 (dist n).

Lemma list_dist_lookup n l1 l2 : l1 ≡{n}≡ l2 ↔ ∀ i, l1 !! i ≡{n}≡ l2 !! i.
Proof. setoid_rewrite dist_option_Forall2. apply Forall2_lookup. Qed.

Global Instance cons_ne : NonExpansive2 (@cons A) := _.
Global Instance app_ne : NonExpansive2 (@app A) := _.
Global Instance length_ne n : Proper (dist n ==> (=)) (@length A) := _.
Global Instance tail_ne : NonExpansive (@tail A) := _.
Global Instance take_ne : NonExpansive (@take A n) := _.
Global Instance drop_ne : NonExpansive (@drop A n) := _.
Global Instance list_lookup_ne i :
  NonExpansive (lookup (M:=list A) i).
Proof. intros ????. by apply dist_option_Forall2, Forall2_lookup. Qed.
Global Instance list_alter_ne n f i :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (alter (M:=list A) f i) := _.
Global Instance list_insert_ne i :
  NonExpansive2 (insert (M:=list A) i) := _.
Global Instance list_inserts_ne i :
  NonExpansive2 (@list_inserts A i) := _.
Global Instance list_delete_ne i :
  NonExpansive (delete (M:=list A) i) := _.
Global Instance option_list_ne : NonExpansive (@option_list A).
Proof. intros ????; by apply Forall2_option_list, dist_option_Forall2. Qed.
Global Instance list_filter_ne n P `{∀ x, Decision (P x)} :
  Proper (dist n ==> iff) P →
  Proper (dist n ==> dist n) (filter (B:=list A) P) := _.
Global Instance replicate_ne :
  NonExpansive (@replicate A n) := _.
Global Instance reverse_ne : NonExpansive (@reverse A) := _.
Global Instance last_ne : NonExpansive (@last A).
Proof. intros ????; by apply dist_option_Forall2, Forall2_last. Qed.
Global Instance resize_ne n :
  NonExpansive2 (@resize A n) := _.

Definition list_ofe_mixin : OfeMixin (list A).
Proof.
  split.
  - intros l k. rewrite equiv_Forall2 -Forall2_forall.
    split; induction 1; constructor; intros; try apply equiv_dist; auto.
  - apply _.
  - rewrite /dist /list_dist. eauto using Forall2_impl, dist_S.
Qed.
Canonical Structure listC := OfeT (list A) list_ofe_mixin.

Program Definition list_chain
    (c : chain listC) (x : A) (k : nat) : chain A :=
  {| chain_car n := from_option id x (c n !! k) |}.
Next Obligation. intros c x k n i ?. by rewrite /= (chain_cauchy c n i). Qed.
Definition list_compl `{Cofe A} : Compl listC := λ c,
  match c 0 with
  | [] => []
  | x :: _ => compl ∘ list_chain c x <$> seq 0 (length (c 0))
  end.
Global Program Instance list_cofe `{Cofe A} : Cofe listC :=
  {| compl := list_compl |}.
Next Obligation.
  intros ? n c; rewrite /compl /list_compl.
  destruct (c 0) as [|x l] eqn:Hc0 at 1.
  { by destruct (chain_cauchy c 0 n); auto with omega. }
  rewrite -(λ H, length_ne _ _ _ (chain_cauchy c 0 n H)); last omega.
  apply Forall2_lookup=> i. rewrite -dist_option_Forall2 list_lookup_fmap.
  destruct (decide (i < length (c n))); last first.
  { rewrite lookup_seq_ge ?lookup_ge_None_2; auto with omega. }
  rewrite lookup_seq //= (conv_compl n (list_chain c _ _)) /=.
  destruct (lookup_lt_is_Some_2 (c n) i) as [? Hcn]; first done.
  by rewrite Hcn.
Qed.

Global Instance list_ofe_discrete : OfeDiscrete A → OfeDiscrete listC.
Proof. induction 2; constructor; try apply (discrete _); auto. Qed.

Global Instance nil_discrete : Discrete (@nil A).
Proof. inversion_clear 1; constructor. Qed.
Global Instance cons_discrete x l : Discrete x → Discrete l → Discrete (x :: l).
Proof. intros ??; inversion_clear 1; constructor; by apply discrete. Qed.
End cofe.

Arguments listC : clear implicits.

(** Functor *)
Lemma list_fmap_ext_ne {A} {B : ofeT} (f g : A → B) (l : list A) n :
  (∀ x, f x ≡{n}≡ g x) → f <$> l ≡{n}≡ g <$> l.
Proof. intros Hf. by apply Forall2_fmap, Forall_Forall2, Forall_true. Qed.
Instance list_fmap_ne {A B : ofeT} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (fmap (M:=list) f).
Proof. intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto. Qed.
Definition listC_map {A B} (f : A -n> B) : listC A -n> listC B :=
  CofeMor (fmap f : listC A → listC B).
Instance listC_map_ne A B : NonExpansive (@listC_map A B).
Proof. intros n f g ? l. by apply list_fmap_ext_ne. Qed.

Program Definition listCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := listC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := listC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>y; apply cFunctor_compose.
Qed.

Instance listCF_contractive F :
  cFunctorContractive F → cFunctorContractive (listCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, cFunctor_contractive.
Qed.

(* CMRA *)
Section cmra.
  Context {A : ucmraT}.
  Implicit Types l : list A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.

  Instance list_op : Op (list A) :=
    fix go l1 l2 := let _ : Op _ := @go in
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1, y :: l2 => x ⋅ y :: l1 ⋅ l2
    end.
  Instance list_pcore : PCore (list A) := λ l, Some (core <$> l).

  Instance list_valid : Valid (list A) := Forall (λ x, ✓ x).
  Instance list_validN : ValidN (list A) := λ n, Forall (λ x, ✓{n} x).

  Lemma cons_valid l x : ✓ (x :: l) ↔ ✓ x ∧ ✓ l.
  Proof. apply Forall_cons. Qed.
  Lemma cons_validN n l x : ✓{n} (x :: l) ↔ ✓{n} x ∧ ✓{n} l.
  Proof. apply Forall_cons. Qed.
  Lemma app_valid l1 l2 : ✓ (l1 ++ l2) ↔ ✓ l1 ∧ ✓ l2.
  Proof. apply Forall_app. Qed.
  Lemma app_validN n l1 l2 : ✓{n} (l1 ++ l2) ↔ ✓{n} l1 ∧ ✓{n} l2.
  Proof. apply Forall_app. Qed.

  Lemma list_lookup_valid l : ✓ l ↔ ∀ i, ✓ (l !! i).
  Proof.
    rewrite {1}/valid /list_valid Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_validN n l : ✓{n} l ↔ ∀ i, ✓{n} (l !! i).
  Proof.
    rewrite {1}/validN /list_validN Forall_lookup; split.
    - intros Hl i. by destruct (l !! i) as [x|] eqn:?; [apply (Hl i)|].
    - intros Hl i x Hi. move: (Hl i); by rewrite Hi.
  Qed.
  Lemma list_lookup_op l1 l2 i : (l1 ⋅ l2) !! i = l1 !! i ⋅ l2 !! i.
  Proof.
    revert i l2. induction l1 as [|x l1]; intros [|i] [|y l2];
      by rewrite /= ?left_id_L ?right_id_L.
  Qed.
  Lemma list_lookup_core l i : core l !! i = core (l !! i).
  Proof.
    rewrite /core /= list_lookup_fmap.
    destruct (l !! i); by rewrite /= ?Some_core.
  Qed.

  Lemma list_lookup_included l1 l2 : l1 ≼ l2 ↔ ∀ i, l1 !! i ≼ l2 !! i.
  Proof.
    split.
    { intros [l Hl] i. exists (l !! i). by rewrite Hl list_lookup_op. }
    revert l1. induction l2 as [|y l2 IH]=>-[|x l1] Hl.
    - by exists [].
    - destruct (Hl 0) as [[z|] Hz]; inversion Hz.
    - by exists (y :: l2).
    - destruct (IH l1) as [l3 ?]; first (intros i; apply (Hl (S i))).
      destruct (Hl 0) as [[z|] Hz]; inversion_clear Hz; simplify_eq/=.
      + exists (z :: l3); by constructor.
      + exists (core x :: l3); constructor; by rewrite ?cmra_core_r.
  Qed.

  Definition list_cmra_mixin : CmraMixin (list A).
  Proof.
    apply cmra_total_mixin.
    - eauto.
    - intros n l l1 l2; rewrite !list_dist_lookup=> Hl i.
      by rewrite !list_lookup_op Hl.
    - intros n l1 l2 Hl; by rewrite /core /= Hl.
    - intros n l1 l2; rewrite !list_dist_lookup !list_lookup_validN=> Hl ? i.
      by rewrite -Hl.
    - intros l. rewrite list_lookup_valid. setoid_rewrite list_lookup_validN.
      setoid_rewrite cmra_valid_validN. naive_solver.
    - intros n x. rewrite !list_lookup_validN. auto using cmra_validN_S.
    - intros l1 l2 l3; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op assoc.
    - intros l1 l2; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_op comm.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite list_lookup_op list_lookup_core cmra_core_l.
    - intros l; rewrite list_equiv_lookup=> i.
      by rewrite !list_lookup_core cmra_core_idemp.
    - intros l1 l2; rewrite !list_lookup_included=> Hl i.
      rewrite !list_lookup_core. by apply cmra_core_mono.
    - intros n l1 l2. rewrite !list_lookup_validN.
      setoid_rewrite list_lookup_op. eauto using cmra_validN_op_l.
    - intros n l.
      induction l as [|x l IH]=> -[|y1 l1] [|y2 l2] Hl Heq;
        (try by exfalso; inversion Heq).
      + by exists [], [].
      + exists [], (x :: l); inversion Heq; by repeat constructor.
      + exists (x :: l), []; inversion Heq; by repeat constructor.
      + destruct (IH l1 l2) as (l1'&l2'&?&?&?),
          (cmra_extend n x y1 y2) as (y1'&y2'&?&?&?);
          [by inversion_clear Heq; inversion_clear Hl..|].
        exists (y1' :: l1'), (y2' :: l2'); repeat constructor; auto.
  Qed.
  Canonical Structure listR := CmraT (list A) list_cmra_mixin.

  Global Instance list_unit : Unit (list A) := [].
  Definition list_ucmra_mixin : UcmraMixin (list A).
  Proof.
    split.
    - constructor.
    - by intros l.
    - by constructor.
  Qed.
  Canonical Structure listUR := UcmraT (list A) list_ucmra_mixin.

  Global Instance list_cmra_discrete : CmraDiscrete A → CmraDiscrete listR.
  Proof.
    split; [apply _|]=> l; rewrite list_lookup_valid list_lookup_validN=> Hl i.
    by apply cmra_discrete_valid.
  Qed.

  Global Instance list_core_id l : (∀ x : A, CoreId x) → CoreId l.
  Proof.
    intros ?; constructor; apply list_equiv_lookup=> i.
    by rewrite list_lookup_core (core_id_core (l !! i)).
  Qed.

  (** Internalized properties *)
  Lemma list_equivI {M} l1 l2 : l1 ≡ l2 ⊣⊢ (∀ i, l1 !! i ≡ l2 !! i : uPred M).
  Proof. uPred.unseal; constructor=> n x ?. apply list_dist_lookup. Qed.
  Lemma list_validI {M} l : ✓ l ⊣⊢ (∀ i, ✓ (l !! i) : uPred M).
  Proof. uPred.unseal; constructor=> n x ?. apply list_lookup_validN. Qed.
End cmra.

Arguments listR : clear implicits.
Arguments listUR : clear implicits.

Instance list_singletonM {A : ucmraT} : SingletonM nat A (list A) := λ n x,
  replicate n ε ++ [x].

Section properties.
  Context {A : ucmraT}.
  Implicit Types l : list A.
  Implicit Types x y z : A.
  Local Arguments op _ _ !_ !_ / : simpl nomatch.
  Local Arguments cmra_op _ !_ !_ / : simpl nomatch.
  Local Arguments ucmra_op _ !_ !_ / : simpl nomatch.

  Lemma list_lookup_opM l mk i : (l ⋅? mk) !! i = l !! i ⋅ (mk ≫= (!! i)).
  Proof. destruct mk; by rewrite /= ?list_lookup_op ?right_id_L. Qed.

  Global Instance list_op_nil_l : LeftId (=) (@nil A) op.
  Proof. done. Qed.
  Global Instance list_op_nil_r : RightId (=) (@nil A) op.
  Proof. by intros []. Qed.

  Lemma list_op_app l1 l2 l3 :
    (l1 ++ l3) ⋅ l2 = (l1 ⋅ take (length l1) l2) ++ (l3 ⋅ drop (length l1) l2).
  Proof.
    revert l2 l3.
    induction l1 as [|x1 l1]=> -[|x2 l2] [|x3 l3]; f_equal/=; auto.
  Qed.
  Lemma list_op_app_le l1 l2 l3 :
    length l2 ≤ length l1 → (l1 ++ l3) ⋅ l2 = (l1 ⋅ l2) ++ l3.
  Proof. intros ?. by rewrite list_op_app take_ge // drop_ge // right_id_L. Qed.

  Lemma list_lookup_validN_Some n l i x : ✓{n} l → l !! i ≡{n}≡ Some x → ✓{n} x.
  Proof. move=> /list_lookup_validN /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.
  Lemma list_lookup_valid_Some l i x : ✓ l → l !! i ≡ Some x → ✓ x.
  Proof. move=> /list_lookup_valid /(_ i)=> Hl Hi; move: Hl. by rewrite Hi. Qed.

  Lemma list_op_length l1 l2 : length (l1 ⋅ l2) = max (length l1) (length l2).
  Proof. revert l2. induction l1; intros [|??]; f_equal/=; auto. Qed.

  Lemma replicate_valid n (x : A) : ✓ x → ✓ replicate n x.
  Proof. apply Forall_replicate. Qed.
  Global Instance list_singletonM_ne i :
    NonExpansive (@list_singletonM A i).
  Proof. intros n l1 l2 ?. apply Forall2_app; by repeat constructor. Qed.
  Global Instance list_singletonM_proper i :
    Proper ((≡) ==> (≡)) (list_singletonM i) := ne_proper _.

  Lemma elem_of_list_singletonM i z x : z ∈ ({[i := x]} : list A) → z = ε ∨ z = x.
  Proof.
    rewrite elem_of_app elem_of_list_singleton elem_of_replicate. naive_solver.
  Qed.
  Lemma list_lookup_singletonM i x : ({[ i := x ]} : list A) !! i = Some x.
  Proof. induction i; by f_equal/=. Qed.
  Lemma list_lookup_singletonM_ne i j x :
    i ≠ j →
    ({[ i := x ]} : list A) !! j = None ∨ ({[ i := x ]} : list A) !! j = Some ε.
  Proof. revert j; induction i; intros [|j]; naive_solver auto with omega. Qed.
  Lemma list_singletonM_validN n i x : ✓{n} ({[ i := x ]} : list A) ↔ ✓{n} x.
  Proof.
    rewrite list_lookup_validN. split.
    { move=> /(_ i). by rewrite list_lookup_singletonM. }
    intros Hx j; destruct (decide (i = j)); subst.
    - by rewrite list_lookup_singletonM.
    - destruct (list_lookup_singletonM_ne i j x) as [Hi|Hi]; first done;
        rewrite Hi; by try apply (ucmra_unit_validN (A:=A)).
  Qed.
  Lemma list_singleton_valid  i x : ✓ ({[ i := x ]} : list A) ↔ ✓ x.
  Proof.
    rewrite !cmra_valid_validN. by setoid_rewrite list_singletonM_validN.
  Qed.
  Lemma list_singletonM_length i x : length {[ i := x ]} = S i.
  Proof.
    rewrite /singletonM /list_singletonM app_length replicate_length /=; lia.
  Qed.

  Lemma list_core_singletonM i (x : A) : core {[ i := x ]} ≡ {[ i := core x ]}.
  Proof.
    rewrite /singletonM /list_singletonM.
    by rewrite {1}/core /= fmap_app fmap_replicate (core_id_core ∅).
  Qed.
  Lemma list_op_singletonM i (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} ≡ {[ i := x ⋅ y ]}.
  Proof.
    rewrite /singletonM /list_singletonM /=.
    induction i; constructor; rewrite ?left_id; auto.
  Qed.
  Lemma list_alter_singletonM f i x :
    alter f i ({[i := x]} : list A) = {[i := f x]}.
  Proof.
    rewrite /singletonM /list_singletonM /=. induction i; f_equal/=; auto.
  Qed.
  Global Instance list_singleton_core_id i (x : A) :
    CoreId x → CoreId {[ i := x ]}.
  Proof. by rewrite !core_id_total list_core_singletonM=> ->. Qed.

  (* Update *)
  Lemma list_singleton_updateP (P : A → Prop) (Q : list A → Prop) x :
    x ~~>: P → (∀ y, P y → Q [y]) → [x] ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup HQ n lf /list_lookup_validN Hv.
    destruct (Hup n (from_option id ε (lf !! 0))) as (y&?&Hv').
    { move: (Hv 0). by destruct lf; rewrite /= ?right_id. }
    exists [y]; split; first by auto.
    apply list_lookup_validN=> i.
    move: (Hv i) Hv'. by destruct i, lf; rewrite /= ?right_id.
  Qed.
  Lemma list_singleton_updateP' (P : A → Prop) x :
    x ~~>: P → [x] ~~>: λ k, ∃ y, k = [y] ∧ P y.
  Proof. eauto using list_singleton_updateP. Qed.
  Lemma list_singleton_update x y : x ~~> y → [x] ~~> [y].
  Proof.
    rewrite !cmra_update_updateP; eauto using list_singleton_updateP with subst.
  Qed.

  Lemma app_updateP (P1 P2 Q : list A → Prop) l1 l2 :
    l1 ~~>: P1 → l2 ~~>: P2 →
    (∀ k1 k2, P1 k1 → P2 k2 → length l1 = length k1 ∧ Q (k1 ++ k2)) →
    l1 ++ l2 ~~>: Q.
  Proof.
    rewrite !cmra_total_updateP=> Hup1 Hup2 HQ n lf.
    rewrite list_op_app app_validN=> -[??].
    destruct (Hup1 n (take (length l1) lf)) as (k1&?&?); auto.
    destruct (Hup2 n (drop (length l1) lf)) as (k2&?&?); auto.
    exists (k1 ++ k2). rewrite list_op_app app_validN.
    by destruct (HQ k1 k2) as [<- ?].
  Qed.
  Lemma app_update l1 l2 k1 k2 :
    length l1 = length k1 →
    l1 ~~> k1 → l2 ~~> k2 → l1 ++ l2 ~~> k1 ++ k2.
  Proof. rewrite !cmra_update_updateP; eauto using app_updateP with subst. Qed.

  Lemma cons_updateP (P1 : A → Prop) (P2 Q : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → (∀ y k, P1 y → P2 k → Q (y :: k)) → x :: l ~~>: Q.
  Proof.
    intros. eapply (app_updateP _ _ _ [x]);
      naive_solver eauto using list_singleton_updateP'.
  Qed.
  Lemma cons_updateP' (P1 : A → Prop) (P2 : list A → Prop) x l :
    x ~~>: P1 → l ~~>: P2 → x :: l ~~>: λ k, ∃ y k', k = y :: k' ∧ P1 y ∧ P2 k'.
  Proof. eauto 10 using cons_updateP. Qed.
  Lemma cons_update x y l k : x ~~> y → l ~~> k → x :: l ~~> y :: k.
  Proof. rewrite !cmra_update_updateP; eauto using cons_updateP with subst. Qed.

  Lemma list_middle_updateP (P : A → Prop) (Q : list A → Prop) l1 x l2 :
    x ~~>: P → (∀ y, P y → Q (l1 ++ y :: l2)) → l1 ++ x :: l2 ~~>: Q.
  Proof.
    intros. eapply app_updateP.
    - by apply cmra_update_updateP.
    - by eapply cons_updateP', cmra_update_updateP.
    - naive_solver.
  Qed.
  Lemma list_middle_update l1 l2 x y : x ~~> y → l1 ++ x :: l2 ~~> l1 ++ y :: l2.
  Proof.
    rewrite !cmra_update_updateP=> ?; eauto using list_middle_updateP with subst.
  Qed.

(* FIXME
  Lemma list_middle_local_update l1 l2 x y ml :
    x ~l~> y @ ml ≫= (!! length l1) →
    l1 ++ x :: l2 ~l~> l1 ++ y :: l2 @ ml.
  Proof.
    intros [Hxy Hxy']; split.
    - intros n; rewrite !list_lookup_validN=> Hl i; move: (Hl i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM; apply (Hxy n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
    - intros n mk; rewrite !list_lookup_validN !list_dist_lookup => Hl Hl' i.
      move: (Hl i) (Hl' i).
      destruct (lt_eq_lt_dec i (length l1)) as [[?|?]|?]; subst.
      + by rewrite !list_lookup_opM !lookup_app_l.
      + rewrite !list_lookup_opM !list_lookup_middle // !Some_op_opM !inj_iff.
        apply (Hxy' n).
      + rewrite !(cons_middle _ l1 l2) !assoc.
        rewrite !list_lookup_opM !lookup_app_r !app_length //=; lia.
  Qed.
  Lemma list_singleton_local_update i x y ml :
    x ~l~> y @ ml ≫= (!! i) → {[ i := x ]} ~l~> {[ i := y ]} @ ml.
  Proof. intros; apply list_middle_local_update. by rewrite replicate_length. Qed.
*)
End properties.

(** Functor *)
Instance list_fmap_cmra_morphism {A B : ucmraT} (f : A → B)
  `{!CmraMorphism f} : CmraMorphism (fmap f : list A → list B).
Proof.
  split; try apply _.
  - intros n l. rewrite !list_lookup_validN=> Hl i. rewrite list_lookup_fmap.
    by apply (cmra_morphism_validN (fmap f : option A → option B)).
  - intros l. apply Some_proper. rewrite -!list_fmap_compose.
    apply list_fmap_equiv_ext, cmra_morphism_core, _.
  - intros l1 l2. apply list_equiv_lookup=>i.
    by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Qed.

Program Definition listURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A B := listUR (urFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := listC_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F ???? n f g Hfg; apply listC_map_ne, urFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(list_fmap_id x).
  apply list_fmap_equiv_ext=>y. apply urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -list_fmap_compose.
  apply list_fmap_equiv_ext=>y; apply urFunctor_compose.
Qed.

Instance listURF_contractive F :
  urFunctorContractive F → urFunctorContractive (listURF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply listC_map_ne, urFunctor_contractive.
Qed.
