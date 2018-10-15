From iris.algebra Require Export cmra.
Set Default Proof Using "Type".

(** The basic definition of the uPred type, its metric and functor laws.
    You probably do not want to import this file. Instead, import
    base_logic.base_logic; that will also give you all the primitive
    and many derived laws for the logic. *)

(* A good way of understanding this definition of the uPred OFE is to
   consider the OFE uPred0 of monotonous SProp predicates. That is,
   uPred0 is the OFE of non-expansive functions from M to SProp that
   are monotonous with respect to CMRA inclusion. This notion of
   monotonicity has to be stated in the SProp logic. Together with the
   usual closedness property of SProp, this gives exactly uPred_mono.

   Then, we quotient uPred0 *in the sProp logic* with respect to
   equivalence on valid elements of M. That is, we quotient with
   respect to the following *sProp* equivalence relation:
     P1 ≡ P2 := ∀ x, ✓ x → (P1(x) ↔ P2(x))       (1)
   When seen from the ambiant logic, obtaining this quotient requires
   definig both a custom Equiv and Dist.


   It is worth noting that this equivalence relation admits canonical
   representatives. More precisely, one can show that every
   equivalence class contains exactly one element P0 such that:
     ∀ x, (✓ x → P0(x)) → P0(x)                 (2)
   (Again, this assertion has to be understood in sProp). Intuitively,
   this says that P0 trivially holds whenever the resource is invalid.
   Starting from any element P, one can find this canonical
   representative by choosing:
     P0(x) := ✓ x → P(x)                        (3)

   Hence, as an alternative definition of uPred, we could use the set
   of canonical representatives (i.e., the subtype of monotonous
   sProp predicates that verify (2)). This alternative definition would
   save us from using a quotient. However, the definitions of the various
   connectives would get more complicated, because we have to make sure
   they all verify (2), which sometimes requires some adjustments. We
   would moreover need to prove one more property for every logical
   connective.
 *)

Record uPred (M : ucmraT) : Type := IProp {
  uPred_holds :> nat → M → Prop;

  uPred_mono n1 n2 x1 x2 :
    uPred_holds n1 x1 → x1 ≼{n1} x2 → n2 ≤ n1 → uPred_holds n2 x2
}.
Arguments uPred_holds {_} _ _ _ : simpl never.
Add Printing Constructor uPred.
Instance: Params (@uPred_holds) 3.

Delimit Scope uPred_scope with I.
Bind Scope uPred_scope with uPred.
Arguments uPred_holds {_} _%I _ _.

Section cofe.
  Context {M : ucmraT}.

  Inductive uPred_equiv' (P Q : uPred M) : Prop :=
    { uPred_in_equiv : ∀ n x, ✓{n} x → P n x ↔ Q n x }.
  Instance uPred_equiv : Equiv (uPred M) := uPred_equiv'.
  Inductive uPred_dist' (n : nat) (P Q : uPred M) : Prop :=
    { uPred_in_dist : ∀ n' x, n' ≤ n → ✓{n'} x → P n' x ↔ Q n' x }.
  Instance uPred_dist : Dist (uPred M) := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin (uPred M).
  Proof.
    split.
    - intros P Q; split.
      + by intros HPQ n; split=> i x ??; apply HPQ.
      + intros HPQ; split=> n x ?; apply HPQ with n; auto.
    - intros n; split.
      + by intros P; split=> x i.
      + by intros P Q HPQ; split=> x i ??; symmetry; apply HPQ.
      + intros P Q Q' HP HQ; split=> i x ??.
        by trans (Q i x);[apply HP|apply HQ].
    - intros n P Q HPQ; split=> i x ??; apply HPQ; auto.
  Qed.
  Canonical Structure uPredC : ofeT := OfeT (uPred M) uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredC := λ c,
    {| uPred_holds n x := ∀ n', n' ≤ n → ✓{n'}x → c n' n' x |}.
  Next Obligation.
    move=> /= c n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv. eapply uPred_mono.
    eapply HP, cmra_validN_includedN, cmra_includedN_le=>//; lia.
    eapply cmra_includedN_le=>//; lia. done.
  Qed.
  Global Program Instance uPred_cofe : Cofe uPredC := {| compl := uPred_compl |}.
  Next Obligation.
    intros n c; split=>i x Hin Hv.
    etrans; [|by symmetry; apply (chain_cauchy c i n)]. split=>H; [by apply H|].
    repeat intro. apply (chain_cauchy c n' i)=>//. by eapply uPred_mono.
  Qed.
End cofe.
Arguments uPredC : clear implicits.

Instance uPred_ne {M} (P : uPred M) n : Proper (dist n ==> iff) (P n).
Proof.
  intros x1 x2 Hx; split=> ?; eapply uPred_mono; eauto; by rewrite Hx.
Qed.
Instance uPred_proper {M} (P : uPred M) n : Proper ((≡) ==> iff) (P n).
Proof. by intros x1 x2 Hx; apply uPred_ne, equiv_dist. Qed.

Lemma uPred_holds_ne {M} (P Q : uPred M) n1 n2 x :
  P ≡{n2}≡ Q → n2 ≤ n1 → ✓{n2} x → Q n1 x → P n2 x.
Proof.
  intros [Hne] ???. eapply Hne; try done. eauto using uPred_mono, cmra_validN_le.
Qed.

(* Equivalence to the definition of uPred in the appendix. *)
Lemma uPred_alt {M : ucmraT} (P: nat → M → Prop) :
  (∀ n1 n2 x1 x2, P n1 x1 → x1 ≼{n1} x2 → n2 ≤ n1 → P n2 x2) ↔
  ( (∀ x n1 n2, n2 ≤ n1 → P n1 x → P n2 x) (* Pointwise down-closed *)
  ∧ (∀ n x1 x2, x1 ≡{n}≡ x2 → ∀ m, m ≤ n → P m x1 ↔ P m x2) (* Non-expansive *)
  ∧ (∀ n x1 x2, x1 ≼{n} x2 → ∀ m, m ≤ n → P m x1 → P m x2) (* Monotonicity *)
  ).
Proof.
  (* Provide this lemma to eauto. *)
  assert (∀ n1 n2 (x1 x2 : M), n2 ≤ n1 → x1 ≡{n1}≡ x2 → x1 ≼{n2} x2).
  { intros ????? H. eapply cmra_includedN_le; last done. by rewrite H. }
  (* Now go ahead. *)
  split.
  - intros Hupred. repeat split; eauto using cmra_includedN_le.
  - intros (Hdown & _ & Hmono) **. eapply Hmono; [done..|]. eapply Hdown; done.
Qed.

(** functor *)
Program Definition uPred_map {M1 M2 : ucmraT} (f : M2 -n> M1)
  `{!CmraMorphism f} (P : uPred M1) :
  uPred M2 := {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, cmra_morphism_monotoneN. Qed.

Instance uPred_map_ne {M1 M2 : ucmraT} (f : M2 -n> M1)
  `{!CmraMorphism f} n : Proper (dist n ==> dist n) (uPred_map f).
Proof.
  intros x1 x2 Hx; split=> n' y ??.
  split; apply Hx; auto using cmra_morphism_validN.
Qed.
Lemma uPred_map_id {M : ucmraT} (P : uPred M): uPred_map cid P ≡ P.
Proof. by split=> n x ?. Qed.
Lemma uPred_map_compose {M1 M2 M3 : ucmraT} (f : M1 -n> M2) (g : M2 -n> M3)
    `{!CmraMorphism f, !CmraMorphism g} (P : uPred M3):
  uPred_map (g ◎ f) P ≡ uPred_map f (uPred_map g P).
Proof. by split=> n x Hx. Qed.
Lemma uPred_map_ext {M1 M2 : ucmraT} (f g : M1 -n> M2)
      `{!CmraMorphism f} `{!CmraMorphism g}:
  (∀ x, f x ≡ g x) → ∀ x, uPred_map f x ≡ uPred_map g x.
Proof. intros Hf P; split=> n x Hx /=; by rewrite /uPred_holds /= Hf. Qed.
Definition uPredC_map {M1 M2 : ucmraT} (f : M2 -n> M1) `{!CmraMorphism f} :
  uPredC M1 -n> uPredC M2 := CofeMor (uPred_map f : uPredC M1 → uPredC M2).
Lemma uPredC_map_ne {M1 M2 : ucmraT} (f g : M2 -n> M1)
    `{!CmraMorphism f, !CmraMorphism g} n :
  f ≡{n}≡ g → uPredC_map f ≡{n}≡ uPredC_map g.
Proof.
  by intros Hfg P; split=> n' y ??;
    rewrite /uPred_holds /= (dist_le _ _ _ _(Hfg y)); last lia.
Qed.

Program Definition uPredCF (F : urFunctor) : cFunctor := {|
  cFunctor_car A B := uPredC (urFunctor_car F B A);
  cFunctor_map A1 A2 B1 B2 fg := uPredC_map (urFunctor_map F (fg.2, fg.1))
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n P Q HPQ.
  apply uPredC_map_ne, urFunctor_ne; split; by apply HPQ.
Qed.
Next Obligation.
  intros F A B P; simpl. rewrite -{2}(uPred_map_id P).
  apply uPred_map_ext=>y. by rewrite urFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' P; simpl. rewrite -uPred_map_compose.
  apply uPred_map_ext=>y; apply urFunctor_compose.
Qed.

Instance uPredCF_contractive F :
  urFunctorContractive F → cFunctorContractive (uPredCF F).
Proof.
  intros ? A1 A2 B1 B2 n P Q HPQ. apply uPredC_map_ne, urFunctor_contractive.
  destruct n; split; by apply HPQ.
Qed.

(** logical entailement *)
Inductive uPred_entails {M} (P Q : uPred M) : Prop :=
  { uPred_in_entails : ∀ n x, ✓{n} x → P n x → Q n x }.
Hint Extern 0 (uPred_entails _ _) => reflexivity.
Instance uPred_entails_rewrite_relation M : RewriteRelation (@uPred_entails M).

Hint Resolve uPred_mono : uPred_def.

(** Notations *)
Notation "P ⊢ Q" := (uPred_entails P%I Q%I)
  (at level 99, Q at level 200, right associativity) : stdpp_scope.
Notation "(⊢)" := uPred_entails (only parsing) : stdpp_scope.
Notation "P ⊣⊢ Q" := (equiv (A:=uPred _) P%I Q%I)
  (at level 95, no associativity) : stdpp_scope.
Notation "(⊣⊢)" := (equiv (A:=uPred _)) (only parsing) : stdpp_scope.

Module uPred.
Section entails.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Global Instance entails_po : PreOrder (@uPred_entails M).
Proof.
  split.
  - by intros P; split=> x i.
  - by intros P Q Q' HP HQ; split=> x i ??; apply HQ, HP.
Qed.
Global Instance entails_anti_sym : AntiSymm (⊣⊢) (@uPred_entails M).
Proof. intros P Q HPQ HQP; split=> x n; by split; [apply HPQ|apply HQP]. Qed.

Lemma equiv_spec P Q : (P ⊣⊢ Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
Proof.
  split; [|by intros [??]; apply (anti_symm (⊢))].
  intros HPQ; split; split=> x i; apply HPQ.
Qed.
Lemma equiv_entails P Q : (P ⊣⊢ Q) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Lemma equiv_entails_sym P Q : (Q ⊣⊢ P) → (P ⊢ Q).
Proof. apply equiv_spec. Qed.
Global Instance entails_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> iff) ((⊢) : relation (uPred M)).
Proof.
  move => P1 P2 /equiv_spec [HP1 HP2] Q1 Q2 /equiv_spec [HQ1 HQ2]; split; intros.
  - by trans P1; [|trans Q1].
  - by trans P2; [|trans Q2].
Qed.
Lemma entails_equiv_l (P Q R : uPred M) : (P ⊣⊢ Q) → (Q ⊢ R) → (P ⊢ R).
Proof. by intros ->. Qed.
Lemma entails_equiv_r (P Q R : uPred M) : (P ⊢ Q) → (Q ⊣⊢ R) → (P ⊢ R).
Proof. by intros ? <-. Qed.

Lemma entails_lim (cP cQ : chain (uPredC M)) :
  (∀ n, cP n ⊢ cQ n) → compl cP ⊢ compl cQ.
Proof.
  intros Hlim; split=> n m ? HP.
  eapply uPred_holds_ne, Hlim, HP; eauto using conv_compl.
Qed.

Lemma limit_preserving_entails `{Cofe A} (Φ Ψ : A → uPred M) :
  NonExpansive Φ → NonExpansive Ψ → LimitPreserving (λ x, Φ x ⊢ Ψ x).
Proof. intros HΦ HΨ c Hc. rewrite -!compl_chain_map /=. by apply entails_lim. Qed.
End entails.
End uPred.
