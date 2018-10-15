From iris.algebra Require Export excl local_updates.
From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import classes.
Set Default Proof Using "Type".

Record auth (A : Type) := Auth { authoritative : excl' A; auth_own : A }.
Add Printing Constructor auth.
Arguments Auth {_} _ _.
Arguments authoritative {_} _.
Arguments auth_own {_} _.
Instance: Params (@Auth) 1.
Instance: Params (@authoritative) 1.
Instance: Params (@auth_own) 1.
Notation "◯ a" := (Auth None a) (at level 20).
Notation "● a" := (Auth (Excl' a) ε) (at level 20).

(* COFE *)
Section cofe.
Context {A : ofeT}.
Implicit Types a : excl' A.
Implicit Types b : A.
Implicit Types x y : auth A.

Instance auth_equiv : Equiv (auth A) := λ x y,
  authoritative x ≡ authoritative y ∧ auth_own x ≡ auth_own y.
Instance auth_dist : Dist (auth A) := λ n x y,
  authoritative x ≡{n}≡ authoritative y ∧ auth_own x ≡{n}≡ auth_own y.

Global Instance Auth_ne : NonExpansive2 (@Auth A).
Proof. by split. Qed.
Global Instance Auth_proper : Proper ((≡) ==> (≡) ==> (≡)) (@Auth A).
Proof. by split. Qed.
Global Instance authoritative_ne: NonExpansive (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance authoritative_proper : Proper ((≡) ==> (≡)) (@authoritative A).
Proof. by destruct 1. Qed.
Global Instance own_ne : NonExpansive (@auth_own A).
Proof. by destruct 1. Qed.
Global Instance own_proper : Proper ((≡) ==> (≡)) (@auth_own A).
Proof. by destruct 1. Qed.

Definition auth_ofe_mixin : OfeMixin (auth A).
Proof. by apply (iso_ofe_mixin (λ x, (authoritative x, auth_own x))). Qed.
Canonical Structure authC := OfeT (auth A) auth_ofe_mixin.

Global Instance auth_cofe `{Cofe A} : Cofe authC.
Proof.
  apply (iso_cofe (λ y : _ * _, Auth (y.1) (y.2))
    (λ x, (authoritative x, auth_own x))); by repeat intro.
Qed.

Global Instance Auth_discrete a b :
  Discrete a → Discrete b → Discrete (Auth a b).
Proof. by intros ?? [??] [??]; split; apply: discrete. Qed.
Global Instance auth_ofe_discrete : OfeDiscrete A → OfeDiscrete authC.
Proof. intros ? [??]; apply _. Qed.
Global Instance auth_leibniz : LeibnizEquiv A → LeibnizEquiv (auth A).
Proof. by intros ? [??] [??] [??]; f_equal/=; apply leibniz_equiv. Qed.
End cofe.

Arguments authC : clear implicits.

(* CMRA *)
Section cmra.
Context {A : ucmraT}.
Implicit Types a b : A.
Implicit Types x y : auth A.

Instance auth_valid : Valid (auth A) := λ x,
  match authoritative x with
  | Excl' a => (∀ n, auth_own x ≼{n} a) ∧ ✓ a
  | None => ✓ auth_own x
  | ExclBot' => False
  end.
Global Arguments auth_valid !_ /.
Instance auth_validN : ValidN (auth A) := λ n x,
  match authoritative x with
  | Excl' a => auth_own x ≼{n} a ∧ ✓{n} a
  | None => ✓{n} auth_own x
  | ExclBot' => False
  end.
Global Arguments auth_validN _ !_ /.
Instance auth_pcore : PCore (auth A) := λ x,
  Some (Auth (core (authoritative x)) (core (auth_own x))).
Instance auth_op : Op (auth A) := λ x y,
  Auth (authoritative x ⋅ authoritative y) (auth_own x ⋅ auth_own y).

Definition auth_valid_eq :
  valid = λ x, match authoritative x with
               | Excl' a => (∀ n, auth_own x ≼{n} a) ∧ ✓ a
               | None => ✓ auth_own x
               | ExclBot' => False
               end := eq_refl _.
Definition auth_validN_eq :
  validN = λ n x, match authoritative x with
                  | Excl' a => auth_own x ≼{n} a ∧ ✓{n} a
                  | None => ✓{n} auth_own x
                  | ExclBot' => False
                  end := eq_refl _.

Lemma auth_included (x y : auth A) :
  x ≼ y ↔ authoritative x ≼ authoritative y ∧ auth_own x ≼ auth_own y.
Proof.
  split; [intros [[z1 z2] Hz]; split; [exists z1|exists z2]; apply Hz|].
  intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto.
Qed.

Lemma authoritative_validN n x : ✓{n} x → ✓{n} authoritative x.
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_own_validN n x : ✓{n} x → ✓{n} auth_own x.
Proof.
  rewrite auth_validN_eq.
  destruct x as [[[]|]]; naive_solver eauto using cmra_validN_includedN.
Qed.

Lemma auth_valid_discrete `{CmraDiscrete A} x :
  ✓ x ↔ match authoritative x with
        | Excl' a => auth_own x ≼ a ∧ ✓ a
        | None => ✓ auth_own x
        | ExclBot' => False
        end.
Proof.
  rewrite auth_valid_eq. destruct x as [[[?|]|] ?]; simpl; try done.
  setoid_rewrite <-cmra_discrete_included_iff; naive_solver eauto using 0.
Qed.
Lemma auth_validN_2 n a b : ✓{n} (● a ⋅ ◯ b) ↔ b ≼{n} a ∧ ✓{n} a.
Proof. by rewrite auth_validN_eq /= left_id. Qed.
Lemma auth_valid_discrete_2 `{CmraDiscrete A} a b : ✓ (● a ⋅ ◯ b) ↔ b ≼ a ∧ ✓ a.
Proof. by rewrite auth_valid_discrete /= left_id. Qed.

Lemma authoritative_valid  x : ✓ x → ✓ authoritative x.
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_own_valid `{CmraDiscrete A} x : ✓ x → ✓ auth_own x.
Proof.
  rewrite auth_valid_discrete.
  destruct x as [[[]|]]; naive_solver eauto using cmra_valid_included.
Qed.

Lemma auth_cmra_mixin : CmraMixin (auth A).
Proof.
  apply cmra_total_mixin.
  - eauto.
  - by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
  - intros n [x a] [y b] [Hx Ha]; simpl in *. rewrite !auth_validN_eq.
    destruct Hx as [?? Hx|]; first destruct Hx; intros ?; ofe_subst; auto.
  - intros [[[?|]|] ?]; rewrite /= ?auth_valid_eq
      ?auth_validN_eq /= ?cmra_included_includedN ?cmra_valid_validN;
      naive_solver eauto using O.
  - intros n [[[]|] ?]; rewrite !auth_validN_eq /=;
      naive_solver eauto using cmra_includedN_S, cmra_validN_S.
  - by split; simpl; rewrite assoc.
  - by split; simpl; rewrite comm.
  - by split; simpl; rewrite ?cmra_core_l.
  - by split; simpl; rewrite ?cmra_core_idemp.
  - intros ??; rewrite! auth_included; intros [??].
    by split; simpl; apply cmra_core_mono.
  - assert (∀ n (a b1 b2 : A), b1 ⋅ b2 ≼{n} a → b1 ≼{n} a).
    { intros n a b1 b2 <-; apply cmra_includedN_l. }
   intros n [[[a1|]|] b1] [[[a2|]|] b2]; rewrite auth_validN_eq;
     naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN.
  - intros n x y1 y2 ? [??]; simpl in *.
    destruct (cmra_extend n (authoritative x) (authoritative y1)
      (authoritative y2)) as (ea1&ea2&?&?&?); auto using authoritative_validN.
    destruct (cmra_extend n (auth_own x) (auth_own y1) (auth_own y2))
      as (b1&b2&?&?&?); auto using auth_own_validN.
    by exists (Auth ea1 b1), (Auth ea2 b2).
Qed.
Canonical Structure authR := CmraT (auth A) auth_cmra_mixin.

Global Instance auth_cmra_discrete : CmraDiscrete A → CmraDiscrete authR.
Proof.
  split; first apply _.
  intros [[[?|]|] ?]; rewrite auth_valid_eq auth_validN_eq /=; auto.
  - setoid_rewrite <-cmra_discrete_included_iff.
    rewrite -cmra_discrete_valid_iff. tauto.
  - by rewrite -cmra_discrete_valid_iff.
Qed.

Instance auth_empty : Unit (auth A) := Auth ε ε.
Lemma auth_ucmra_mixin : UcmraMixin (auth A).
Proof.
  split; simpl.
  - rewrite auth_valid_eq /=. apply ucmra_unit_valid.
  - by intros x; constructor; rewrite /= left_id.
  - do 2 constructor; simpl; apply (core_id_core _).
Qed.
Canonical Structure authUR := UcmraT (auth A) auth_ucmra_mixin.

Global Instance auth_frag_core_id a : CoreId a → CoreId (◯ a).
Proof. do 2 constructor; simpl; auto. by apply core_id_core. Qed.

(** Internalized properties *)
Lemma auth_equivI {M} (x y : auth A) :
  x ≡ y ⊣⊢ (authoritative x ≡ authoritative y ∧ auth_own x ≡ auth_own y : uPred M).
Proof. by uPred.unseal. Qed.
Lemma auth_validI {M} (x : auth A) :
  ✓ x ⊣⊢ (match authoritative x with
          | Excl' a => (∃ b, a ≡ auth_own x ⋅ b) ∧ ✓ a
          | None => ✓ auth_own x
          | ExclBot' => False
          end : uPred M).
Proof. uPred.unseal. by destruct x as [[[]|]]. Qed.

Lemma auth_frag_op a b : ◯ (a ⋅ b) = ◯ a ⋅ ◯ b.
Proof. done. Qed.
Lemma auth_frag_mono a b : a ≼ b → ◯ a ≼ ◯ b.
Proof. intros [c ->]. rewrite auth_frag_op. apply cmra_included_l. Qed.

Global Instance auth_frag_sep_homomorphism :
  MonoidHomomorphism op op (≡) (@Auth A None).
Proof. by split; [split; try apply _|]. Qed.

Lemma auth_both_op a b : Auth (Excl' a) b ≡ ● a ⋅ ◯ b.
Proof. by rewrite /op /auth_op /= left_id. Qed.
Lemma auth_auth_valid a : ✓ a → ✓ (● a).
Proof. intros; split; simpl; auto using ucmra_unit_leastN. Qed.

Lemma auth_update a b a' b' :
  (a,b) ~l~> (a',b') → ● a ⋅ ◯ b ~~> ● a' ⋅ ◯ b'.
Proof.
  intros Hup; apply cmra_total_update.
  move=> n [[[?|]|] bf1] // [[bf2 Ha] ?]; do 2 red; simpl in *.
  move: Ha; rewrite !left_id -assoc=> Ha.
  destruct (Hup n (Some (bf1 ⋅ bf2))); auto.
  split; last done. exists bf2. by rewrite -assoc.
Qed.

Lemma auth_update_alloc a a' b' : (a,ε) ~l~> (a',b') → ● a ~~> ● a' ⋅ ◯ b'.
Proof. intros. rewrite -(right_id _ _ (● a)). by apply auth_update. Qed.
Lemma auth_update_dealloc a b a' : (a,b) ~l~> (a',ε) → ● a ⋅ ◯ b ~~> ● a'.
Proof. intros. rewrite -(right_id _ _ (● a')). by apply auth_update. Qed.

Lemma auth_local_update (a b0 b1 a' b0' b1': A) :
  (b0, b1) ~l~> (b0', b1') → b0' ≼ a' → ✓ a' →
  (● a ⋅ ◯ b0, ● a ⋅ ◯ b1) ~l~> (● a' ⋅ ◯ b0', ● a' ⋅ ◯ b1').
Proof.
  rewrite !local_update_unital=> Hup ? ? n /=.
  move=> [[[ac|]|] bc] /auth_validN_2 [Le Val] [] /=;
    inversion_clear 1 as [?? Ha|]; inversion_clear Ha. (* need setoid_discriminate! *)
  rewrite !left_id=> ?.
  destruct (Hup n bc) as [Hval' Heq]; eauto using cmra_validN_includedN.
  rewrite -!auth_both_op auth_validN_eq /=.
  split_and!; [by apply cmra_included_includedN|by apply cmra_valid_validN|done].
Qed.
End cmra.

Arguments authR : clear implicits.
Arguments authUR : clear implicits.

(* Proof mode class instances *)
Instance is_op_auth_frag {A : ucmraT} (a b1 b2 : A) :
  IsOp a b1 b2 → IsOp' (◯ a) (◯ b1) (◯ b2).
Proof. done. Qed.

(* Functor *)
Definition auth_map {A B} (f : A → B) (x : auth A) : auth B :=
  Auth (excl_map f <$> authoritative x) (f (auth_own x)).
Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_map_compose {A B C} (f : A → B) (g : B → C) (x : auth A) :
  auth_map (g ∘ f) x = auth_map g (auth_map f x).
Proof. by destruct x as [[[]|]]. Qed.
Lemma auth_map_ext {A B : ofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → auth_map f x ≡ auth_map g x.
Proof.
  constructor; simpl; auto.
  apply option_fmap_equiv_ext=> a; by apply excl_map_ext.
Qed.
Instance auth_map_ne {A B : ofeT} n :
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@auth_map A B).
Proof.
  intros f g Hf [??] [??] [??]; split; simpl in *; [|by apply Hf].
  apply option_fmap_ne; [|done]=> x y ?; by apply excl_map_ne.
Qed.
Instance auth_map_cmra_morphism {A B : ucmraT} (f : A → B) :
  CmraMorphism f → CmraMorphism (auth_map f).
Proof.
  split; try apply _.
  - intros n [[[a|]|] b]; rewrite !auth_validN_eq; try
      naive_solver eauto using cmra_morphism_monotoneN, cmra_morphism_validN.
  - intros [??]. apply Some_proper; rewrite /auth_map /=.
    by f_equiv; rewrite /= cmra_morphism_core.
  - intros [[?|]?] [[?|]?]; try apply Auth_proper=>//=; by rewrite cmra_morphism_op.
Qed.
Definition authC_map {A B} (f : A -n> B) : authC A -n> authC B :=
  CofeMor (auth_map f).
Lemma authC_map_ne A B : NonExpansive (@authC_map A B).
Proof. intros n f f' Hf [[[a|]|] b]; repeat constructor; apply Hf. Qed.

Program Definition authRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A B := authR (urFunctor_car F A B);
  rFunctor_map A1 A2 B1 B2 fg := authC_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(auth_map_id x).
  apply auth_map_ext=>y; apply urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -auth_map_compose.
  apply auth_map_ext=>y; apply urFunctor_compose.
Qed.

Instance authRF_contractive F :
  urFunctorContractive F → rFunctorContractive (authRF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_contractive.
Qed.

Program Definition authURF (F : urFunctor) : urFunctor := {|
  urFunctor_car A B := authUR (urFunctor_car F A B);
  urFunctor_map A1 A2 B1 B2 fg := authC_map (urFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(auth_map_id x).
  apply auth_map_ext=>y; apply urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -auth_map_compose.
  apply auth_map_ext=>y; apply urFunctor_compose.
Qed.

Instance authURF_contractive F :
  urFunctorContractive F → urFunctorContractive (authURF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply authC_map_ne, urFunctor_contractive.
Qed.
