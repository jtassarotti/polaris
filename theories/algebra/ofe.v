From iris.algebra Require Export base.
Set Default Proof Using "Type".

(** This files defines (a shallow embedding of) the category of OFEs:
    Complete ordered families of equivalences. This is a cartesian closed
    category, and mathematically speaking, the entire development lives
    in this category. However, we will generally prefer to work with raw
    Coq functions plus some registered Proper instances for non-expansiveness.
    This makes writing such functions much easier. It turns out that it many 
    cases, we do not even need non-expansiveness.
*)

(** Unbundeled version *)
Class Dist A := dist : nat → relation A.
Instance: Params (@dist) 3.
Notation "x ≡{ n }≡ y" := (dist n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Hint Extern 0 (_ ≡{_}≡ _) => reflexivity.
Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption.
Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).

Tactic Notation "ofe_subst" ident(x) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.
Tactic Notation "ofe_subst" :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | H:@dist ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist A d n) x
  | H:@dist ?A ?d ?n _ ?x |- _ => symmetry in H;setoid_subst_aux (@dist A d n) x
  end.

Section mixin.
  Local Set Primitive Projections.
  Record OfeMixin A `{Equiv A, Dist A} := {
    mixin_equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y;
    mixin_dist_equivalence n : Equivalence (dist n);
    mixin_dist_S n x y : x ≡{S n}≡ y → x ≡{n}≡ y
  }.
End mixin.

(** Bundeled version *)
Structure ofeT := OfeT' {
  ofe_car :> Type;
  ofe_equiv : Equiv ofe_car;
  ofe_dist : Dist ofe_car;
  ofe_mixin : OfeMixin ofe_car;
  _ : Type
}.
Arguments OfeT' _ {_ _} _ _.
Notation OfeT A m := (OfeT' A m A).
Add Printing Constructor ofeT.
Hint Extern 0 (Equiv _) => eapply (@ofe_equiv _) : typeclass_instances.
Hint Extern 0 (Dist _) => eapply (@ofe_dist _) : typeclass_instances.
Arguments ofe_car : simpl never.
Arguments ofe_equiv : simpl never.
Arguments ofe_dist : simpl never.
Arguments ofe_mixin : simpl never.

(** When declaring instances of subclasses of OFE (like CMRAs and unital CMRAs)
we need Coq to *infer* the canonical OFE instance of a given type and take the
mixin out of it. This makes sure we do not use two different OFE instances in
different places (see for example the constructors [CmraT] and [UcmraT] in the
file [cmra.v].)

In order to infer the OFE instance, we use the definition [ofe_mixin_of'] which
is inspired by the [clone] trick in ssreflect. It works as follows, when type
checking [@ofe_mixin_of' A ?Ac id] Coq faces a unification problem:

  ofe_car ?Ac  ~  A

which will resolve [?Ac] to the canonical OFE instance corresponding to [A]. The
definition [@ofe_mixin_of' A ?Ac id] will then provide the corresponding mixin.
Note that type checking of [ofe_mixin_of' A id] will fail when [A] does not have
a canonical OFE instance.

The notation [ofe_mixin_of A] that we define on top of [ofe_mixin_of' A id]
hides the [id] and normalizes the mixin to head normal form. The latter is to
ensure that we do not end up with redundant canonical projections to the mixin,
i.e. them all being of the shape [ofe_mixin_of' A id]. *)
Definition ofe_mixin_of' A {Ac : ofeT} (f : Ac → A) : OfeMixin Ac := ofe_mixin Ac.
Notation ofe_mixin_of A :=
  ltac:(let H := eval hnf in (ofe_mixin_of' A id) in exact H) (only parsing).

(** Lifting properties from the mixin *)
Section ofe_mixin.
  Context {A : ofeT}.
  Implicit Types x y : A.
  Lemma equiv_dist x y : x ≡ y ↔ ∀ n, x ≡{n}≡ y.
  Proof. apply (mixin_equiv_dist _ (ofe_mixin A)). Qed.
  Global Instance dist_equivalence n : Equivalence (@dist A _ n).
  Proof. apply (mixin_dist_equivalence _ (ofe_mixin A)). Qed.
  Lemma dist_S n x y : x ≡{S n}≡ y → x ≡{n}≡ y.
  Proof. apply (mixin_dist_S _ (ofe_mixin A)). Qed.
End ofe_mixin.

Hint Extern 1 (_ ≡{_}≡ _) => apply equiv_dist; assumption.

(** Discrete OFEs and discrete OFE elements *)
Class Discrete {A : ofeT} (x : A) := discrete y : x ≡{0}≡ y → x ≡ y.
Arguments discrete {_} _ {_} _ _.
Hint Mode Discrete + ! : typeclass_instances.
Instance: Params (@Discrete) 1.

Class OfeDiscrete (A : ofeT) := ofe_discrete_discrete (x : A) :> Discrete x.

(** OFEs with a completion *)
Record chain (A : ofeT) := {
  chain_car :> nat → A;
  chain_cauchy n i : n ≤ i → chain_car i ≡{n}≡ chain_car n
}.
Arguments chain_car {_} _ _.
Arguments chain_cauchy {_} _ _ _ _.

Program Definition chain_map {A B : ofeT} (f : A → B)
    `{!NonExpansive f} (c : chain A) : chain B :=
  {| chain_car n := f (c n) |}.
Next Obligation. by intros A B f Hf c n i ?; apply Hf, chain_cauchy. Qed.

Notation Compl A := (chain A%type → A).
Class Cofe (A : ofeT) := {
  compl : Compl A;
  conv_compl n c : compl c ≡{n}≡ c n;
}.
Arguments compl : simpl never.

Lemma compl_chain_map `{Cofe A, Cofe B} (f : A → B) c `(NonExpansive f) :
  compl (chain_map f c) ≡ f (compl c).
Proof. apply equiv_dist=>n. by rewrite !conv_compl. Qed.

Program Definition chain_const {A : ofeT} (a : A) : chain A :=
  {| chain_car n := a |}.
Next Obligation. by intros A a n i _. Qed.

Lemma compl_chain_const {A : ofeT} `{!Cofe A} (a : A) :
  compl (chain_const a) ≡ a.
Proof. apply equiv_dist=>n. by rewrite conv_compl. Qed.

(** General properties *)
Section ofe.
  Context {A : ofeT}.
  Implicit Types x y : A.
  Global Instance ofe_equivalence : Equivalence ((≡) : relation A).
  Proof.
    split.
    - by intros x; rewrite equiv_dist.
    - by intros x y; rewrite !equiv_dist.
    - by intros x y z; rewrite !equiv_dist; intros; trans y.
  Qed.
  Global Instance dist_ne n : Proper (dist n ==> dist n ==> iff) (@dist A _ n).
  Proof.
    intros x1 x2 ? y1 y2 ?; split; intros.
    - by trans x1; [|trans y1].
    - by trans x2; [|trans y2].
  Qed.
  Global Instance dist_proper n : Proper ((≡) ==> (≡) ==> iff) (@dist A _ n).
  Proof.
    by move => x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
  Qed.
  Global Instance dist_proper_2 n x : Proper ((≡) ==> iff) (dist n x).
  Proof. by apply dist_proper. Qed.
  Global Instance Discrete_proper : Proper ((≡) ==> iff) (@Discrete A).
  Proof. intros x y Hxy. rewrite /Discrete. by setoid_rewrite Hxy. Qed.

  Lemma dist_le n n' x y : x ≡{n}≡ y → n' ≤ n → x ≡{n'}≡ y.
  Proof. induction 2; eauto using dist_S. Qed.
  Lemma dist_le' n n' x y : n' ≤ n → x ≡{n}≡ y → x ≡{n'}≡ y.
  Proof. intros; eauto using dist_le. Qed.
  Instance ne_proper {B : ofeT} (f : A → B) `{!NonExpansive f} :
    Proper ((≡) ==> (≡)) f | 100.
  Proof. by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n). Qed.
  Instance ne_proper_2 {B C : ofeT} (f : A → B → C) `{!NonExpansive2 f} :
    Proper ((≡) ==> (≡) ==> (≡)) f | 100.
  Proof.
     unfold Proper, respectful; setoid_rewrite equiv_dist.
     by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
  Qed.

  Lemma conv_compl' `{Cofe A} n (c : chain A) : compl c ≡{n}≡ c (S n).
  Proof.
    transitivity (c n); first by apply conv_compl. symmetry.
    apply chain_cauchy. omega.
  Qed.

  Lemma discrete_iff n (x : A) `{!Discrete x} y : x ≡ y ↔ x ≡{n}≡ y.
  Proof.
    split; intros; auto. apply (discrete _), dist_le with n; auto with lia.
  Qed.
  Lemma discrete_iff_0 n (x : A) `{!Discrete x} y : x ≡{0}≡ y ↔ x ≡{n}≡ y.
  Proof. by rewrite -!discrete_iff. Qed.
End ofe.

(** Contractive functions *)
Definition dist_later `{Dist A} (n : nat) (x y : A) : Prop :=
  match n with 0 => True | S n => x ≡{n}≡ y end.
Arguments dist_later _ _ !_ _ _ /.

Global Instance dist_later_equivalence (A : ofeT) n : Equivalence (@dist_later A _ n).
Proof. destruct n as [|n]. by split. apply dist_equivalence. Qed.

Lemma dist_dist_later {A : ofeT} n (x y : A) : dist n x y → dist_later n x y.
Proof. intros Heq. destruct n; first done. exact: dist_S. Qed.

Lemma dist_later_dist {A : ofeT} n (x y : A) : dist_later (S n) x y → dist n x y.
Proof. done. Qed.

(* We don't actually need this lemma (as our tactics deal with this through
   other means), but technically speaking, this is the reason why
   pre-composing a non-expansive function to a contractive function
   preserves contractivity. *)
Lemma ne_dist_later {A B : ofeT} (f : A → B) :
  NonExpansive f → ∀ n, Proper (dist_later n ==> dist_later n) f.
Proof. intros Hf [|n]; last exact: Hf. hnf. by intros. Qed.

Notation Contractive f := (∀ n, Proper (dist_later n ==> dist n) f).

Instance const_contractive {A B : ofeT} (x : A) : Contractive (@const A B x).
Proof. by intros n y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context {A B : ofeT} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{0}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.
  Lemma contractive_S n x y : x ≡{n}≡ y → f x ≡{S n}≡ f y.
  Proof. intros. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof. by intros n x y ?; apply dist_S, contractive_S. Qed.
  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. apply (ne_proper _). Qed.
End contractive.

Ltac f_contractive :=
  match goal with
  | |- ?f _ ≡{_}≡ ?f _ => simple apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ ≡{_}≡ ?f _ _ => simple apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  end;
  try match goal with
  | |- @dist_later ?A _ ?n ?x ?y =>
         destruct n as [|n]; [exact I|change (@dist A _ n x y)]
  end;
  try simple apply reflexivity.

Ltac solve_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_equiv]).

(** Limit preserving predicates *)
Class LimitPreserving `{!Cofe A} (P : A → Prop) : Prop :=
  limit_preserving (c : chain A) : (∀ n, P (c n)) → P (compl c).
Hint Mode LimitPreserving + + ! : typeclass_instances.

Section limit_preserving.
  Context `{Cofe A}.
  (* These are not instances as they will never fire automatically...
     but they can still be helpful in proving things to be limit preserving. *)

  Lemma limit_preserving_ext (P Q : A → Prop) :
    (∀ x, P x ↔ Q x) → LimitPreserving P → LimitPreserving Q.
  Proof. intros HP Hlimit c ?. apply HP, Hlimit=> n; by apply HP. Qed.

  Global Instance limit_preserving_const (P : Prop) : LimitPreserving (λ _, P).
  Proof. intros c HP. apply (HP 0). Qed.

  Lemma limit_preserving_discrete (P : A → Prop) :
    Proper (dist 0 ==> impl) P → LimitPreserving P.
  Proof. intros PH c Hc. by rewrite (conv_compl 0). Qed.

  Lemma limit_preserving_and (P1 P2 : A → Prop) :
    LimitPreserving P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x ∧ P2 x).
  Proof. intros Hlim1 Hlim2 c Hc. split. apply Hlim1, Hc. apply Hlim2, Hc. Qed.

  Lemma limit_preserving_impl (P1 P2 : A → Prop) :
    Proper (dist 0 ==> impl) P1 → LimitPreserving P2 →
    LimitPreserving (λ x, P1 x → P2 x).
  Proof.
    intros Hlim1 Hlim2 c Hc HP1. apply Hlim2=> n; apply Hc.
    eapply Hlim1, HP1. apply dist_le with n; last lia. apply (conv_compl n).
  Qed.

  Lemma limit_preserving_forall {B} (P : B → A → Prop) :
    (∀ y, LimitPreserving (P y)) →
    LimitPreserving (λ x, ∀ y, P y x).
  Proof. intros Hlim c Hc y. by apply Hlim. Qed.
End limit_preserving.

(** Fixpoint *)
Program Definition fixpoint_chain {A : ofeT} `{Inhabited A} (f : A → A)
  `{!Contractive f} : chain A := {| chain_car i := Nat.iter (S i) f inhabitant |}.
Next Obligation.
  intros A ? f ? n.
  induction n as [|n IH]=> -[|i] //= ?; try omega.
  - apply (contractive_0 f).
  - apply (contractive_S f), IH; auto with omega.
Qed.

Program Definition fixpoint_def `{Cofe A, Inhabited A} (f : A → A)
  `{!Contractive f} : A := compl (fixpoint_chain f).
Definition fixpoint_aux : seal (@fixpoint_def). by eexists. Qed.
Definition fixpoint {A AC AiH} f {Hf} := unseal fixpoint_aux A AC AiH f Hf.
Definition fixpoint_eq : @fixpoint = @fixpoint_def := seal_eq fixpoint_aux.

Section fixpoint.
  Context `{Cofe A, Inhabited A} (f : A → A) `{!Contractive f}.

  Lemma fixpoint_unfold : fixpoint f ≡ f (fixpoint f).
  Proof.
    apply equiv_dist=>n.
    rewrite fixpoint_eq /fixpoint_def (conv_compl n (fixpoint_chain f)) //.
    induction n as [|n IH]; simpl; eauto using contractive_0, contractive_S.
  Qed.

  Lemma fixpoint_unique (x : A) : x ≡ f x → x ≡ fixpoint f.
  Proof.
    rewrite !equiv_dist=> Hx n. induction n as [|n IH]; simpl in *.
    - rewrite Hx fixpoint_unfold; eauto using contractive_0.
    - rewrite Hx fixpoint_unfold. apply (contractive_S _), IH.
  Qed.

  Lemma fixpoint_ne (g : A → A) `{!Contractive g} n :
    (∀ z, f z ≡{n}≡ g z) → fixpoint f ≡{n}≡ fixpoint g.
  Proof.
    intros Hfg. rewrite fixpoint_eq /fixpoint_def
      (conv_compl n (fixpoint_chain f)) (conv_compl n (fixpoint_chain g)) /=.
    induction n as [|n IH]; simpl in *; [by rewrite !Hfg|].
    rewrite Hfg; apply contractive_S, IH; auto using dist_S.
  Qed.
  Lemma fixpoint_proper (g : A → A) `{!Contractive g} :
    (∀ x, f x ≡ g x) → fixpoint f ≡ fixpoint g.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne. Qed.

  Lemma fixpoint_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpoint f).
  Proof.
    intros ? [x Hx] Hincr Hlim. set (chcar i := Nat.iter (S i) f x).
    assert (Hcauch : ∀ n i : nat, n ≤ i → chcar i ≡{n}≡ chcar n).
    { intros n. rewrite /chcar. induction n as [|n IH]=> -[|i] //=;
        eauto using contractive_0, contractive_S with omega. }
    set (fp2 := compl {| chain_cauchy := Hcauch |}).
    assert (f fp2 ≡ fp2).
    { apply equiv_dist=>n. rewrite /fp2 (conv_compl n) /= /chcar.
      induction n as [|n IH]; simpl; eauto using contractive_0, contractive_S. }
    rewrite -(fixpoint_unique fp2) //.
    apply Hlim=> n /=. by apply Nat_iter_ind.
  Qed.
End fixpoint.


(** Fixpoint of f when f^k is contractive. **)
Definition fixpointK `{Cofe A, Inhabited A} k (f : A → A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).

Section fixpointK.
  Local Set Default Proof Using "Type*".
  Context `{Cofe A, Inhabited A} (f : A → A) (k : nat).
  Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.
  (* Note than f_ne is crucial here:  there are functions f such that f^2 is contractive,
     but f is not non-expansive.
     Consider for example f: SPred → SPred (where SPred is "downclosed sets of natural numbers").
     Define f (using informative excluded middle) as follows:
     f(N) = N  (where N is the set of all natural numbers)
     f({0, ..., n}) = {0, ... n-1}  if n is even (so n-1 is at least -1, in which case we return the empty set)
     f({0, ..., n}) = {0, ..., n+2} if n is odd
     In other words, if we consider elements of SPred as ordinals, then we decreaste odd finite
     ordinals by 1 and increase even finite ordinals by 2.
     f is not non-expansive:  Consider f({0}) = ∅ and f({0,1}) = f({0,1,2,3}).
     The arguments are clearly 0-equal, but the results are not.

     Now consider g := f^2. We have
     g(N) = N
     g({0, ..., n}) = {0, ... n+1}  if n is even
     g({0, ..., n}) = {0, ..., n+4} if n is odd
     g is contractive.  All outputs contain 0, so they are all 0-equal.
     Now consider two n-equal inputs. We have to show that the outputs are n+1-equal.
     Either they both do not contain n in which case they have to be fully equal and
     hence so are the results.  Or else they both contain n, so the results will
     both contain n+1, so the results are n+1-equal.
   *)

  Let f_proper : Proper ((≡) ==> (≡)) f := ne_proper f.
  Local Existing Instance f_proper.

  Lemma fixpointK_unfold : fixpointK k f ≡ f (fixpointK k f).
  Proof.
    symmetry. rewrite /fixpointK. apply fixpoint_unique.
    by rewrite -Nat_iter_S_r Nat_iter_S -fixpoint_unfold.
  Qed.

  Lemma fixpointK_unique (x : A) : x ≡ f x → x ≡ fixpointK k f.
  Proof.
    intros Hf. apply fixpoint_unique. clear f_contractive.
    induction k as [|k' IH]=> //=. by rewrite -IH.
  Qed.

  Section fixpointK_ne.
    Context (g : A → A) `{g_contractive : !Contractive (Nat.iter k g)}.
    Context {g_ne : NonExpansive g}.

    Lemma fixpointK_ne n : (∀ z, f z ≡{n}≡ g z) → fixpointK k f ≡{n}≡ fixpointK k g.
    Proof.
      rewrite /fixpointK=> Hfg /=. apply fixpoint_ne=> z.
      clear f_contractive g_contractive.
      induction k as [|k' IH]=> //=. by rewrite IH Hfg.
    Qed.

    Lemma fixpointK_proper : (∀ z, f z ≡ g z) → fixpointK k f ≡ fixpointK k g.
    Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne. Qed.
  End fixpointK_ne.

  Lemma fixpointK_ind (P : A → Prop) :
    Proper ((≡) ==> impl) P →
    (∃ x, P x) → (∀ x, P x → P (f x)) →
    LimitPreserving P →
    P (fixpointK k f).
  Proof.
    intros. rewrite /fixpointK. apply fixpoint_ind; eauto.
    intros; apply Nat_iter_ind; auto.
  Qed.
End fixpointK.

(** Mutual fixpoints *)
Section fixpointAB.
  Local Unset Default Proof Using.

  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA : A → B → A).
  Context (fB : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.

  Local Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
  Local Instance fixpoint_AB_contractive : Contractive fixpoint_AB.
  Proof.
    intros n x x' Hx; rewrite /fixpoint_AB.
    apply fixpoint_ne=> y. by f_contractive.
  Qed.

  Local Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
  Local Instance fixpoint_AA_contractive : Contractive fixpoint_AA.
  Proof. solve_contractive. Qed.

  Definition fixpoint_A : A := fixpoint fixpoint_AA.
  Definition fixpoint_B : B := fixpoint_AB fixpoint_A.

  Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B ≡ fixpoint_A.
  Proof. by rewrite {2}/fixpoint_A (fixpoint_unfold _). Qed.
  Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B ≡ fixpoint_B.
  Proof. by rewrite {2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _). Qed.

  Instance: Proper ((≡) ==> (≡) ==> (≡)) fA.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.
  Instance: Proper ((≡) ==> (≡) ==> (≡)) fB.
  Proof.
    apply ne_proper_2=> n x x' ? y y' ?. f_contractive; auto using dist_S.
  Qed.

  Lemma fixpoint_A_unique p q : fA p q ≡ p → fB p q ≡ q → p ≡ fixpoint_A.
  Proof.
    intros HfA HfB. rewrite -HfA. apply fixpoint_unique. rewrite /fixpoint_AA.
    f_equiv=> //. apply fixpoint_unique. by rewrite HfA HfB.
  Qed.
  Lemma fixpoint_B_unique p q : fA p q ≡ p → fB p q ≡ q → q ≡ fixpoint_B.
  Proof. intros. apply fixpoint_unique. by rewrite -fixpoint_A_unique. Qed.
End fixpointAB.

Section fixpointAB_ne.
  Context `{Cofe A, Cofe B, !Inhabited A, !Inhabited B}.
  Context (fA fA' : A → B → A).
  Context (fB fB' : A → B → B).
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA}.
  Context `{∀ n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
  Context `{∀ n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.

  Lemma fixpoint_A_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_A fA fB ≡{n}≡ fixpoint_A fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z.
    rewrite /fixpoint_AA /fixpoint_AB HfA. f_equiv. by apply fixpoint_ne.
  Qed.
  Lemma fixpoint_B_ne n :
    (∀ x y, fA x y ≡{n}≡ fA' x y) → (∀ x y, fB x y ≡{n}≡ fB' x y) →
    fixpoint_B fA fB ≡{n}≡ fixpoint_B fA' fB'.
  Proof.
    intros HfA HfB. apply fixpoint_ne=> z. rewrite HfB. f_contractive.
    apply fixpoint_A_ne; auto using dist_S.
  Qed.

  Lemma fixpoint_A_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_A fA fB ≡ fixpoint_A fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne. Qed.
  Lemma fixpoint_B_proper :
    (∀ x y, fA x y ≡ fA' x y) → (∀ x y, fB x y ≡ fB' x y) →
    fixpoint_B fA fB ≡ fixpoint_B fA' fB'.
  Proof. setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne. Qed.
End fixpointAB_ne.

(** Non-expansive function space *)
Record ofe_mor (A B : ofeT) : Type := CofeMor {
  ofe_mor_car :> A → B;
  ofe_mor_ne : NonExpansive ofe_mor_car
}.
Arguments CofeMor {_ _} _ {_}.
Add Printing Constructor ofe_mor.
Existing Instance ofe_mor_ne.

Notation "'λne' x .. y , t" :=
  (@CofeMor _ _ (λ x, .. (@CofeMor _ _ (λ y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).

Section ofe_mor.
  Context {A B : ofeT}.
  Global Instance ofe_mor_proper (f : ofe_mor A B) : Proper ((≡) ==> (≡)) f.
  Proof. apply ne_proper, ofe_mor_ne. Qed.
  Instance ofe_mor_equiv : Equiv (ofe_mor A B) := λ f g, ∀ x, f x ≡ g x.
  Instance ofe_mor_dist : Dist (ofe_mor A B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure ofe_morC := OfeT (ofe_mor A B) ofe_mor_ofe_mixin.

  Program Definition ofe_mor_chain (c : chain ofe_morC)
    (x : A) : chain B := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Program Definition ofe_mor_compl `{Cofe B} : Compl ofe_morC := λ c,
    {| ofe_mor_car x := compl (ofe_mor_chain c x) |}.
  Next Obligation.
    intros ? c n x y Hx. by rewrite (conv_compl n (ofe_mor_chain c x))
      (conv_compl n (ofe_mor_chain c y)) /= Hx.
  Qed.
  Global Program Instance ofe_mor_cofe `{Cofe B} : Cofe ofe_morC :=
    {| compl := ofe_mor_compl |}.
  Next Obligation.
    intros ? n c x; simpl.
    by rewrite (conv_compl n (ofe_mor_chain c x)) /=.
  Qed.

  Global Instance ofe_mor_car_ne :
    NonExpansive2 (@ofe_mor_car A B).
  Proof. intros n f g Hfg x y Hx; rewrite Hx; apply Hfg. Qed.
  Global Instance ofe_mor_car_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (@ofe_mor_car A B) := ne_proper_2 _.
  Lemma ofe_mor_ext (f g : ofe_mor A B) : f ≡ g ↔ ∀ x, f x ≡ g x.
  Proof. done. Qed.
End ofe_mor.

Arguments ofe_morC : clear implicits.
Notation "A -n> B" :=
  (ofe_morC A B) (at level 99, B at level 200, right associativity).
Instance ofe_mor_inhabited {A B : ofeT} `{Inhabited B} :
  Inhabited (A -n> B) := populate (λne _, inhabitant).

(** Identity and composition and constant function *)
Definition cid {A} : A -n> A := CofeMor id.
Instance: Params (@cid) 1.
Definition cconst {A B : ofeT} (x : B) : A -n> B := CofeMor (const x).
Instance: Params (@cconst) 2.

Definition ccompose {A B C}
  (f : B -n> C) (g : A -n> B) : A -n> C := CofeMor (f ∘ g).
Instance: Params (@ccompose) 3.
Infix "◎" := ccompose (at level 40, left associativity).
Global Instance ccompose_ne {A B C} :
  NonExpansive2 (@ccompose A B C).
Proof. intros n ?? Hf g1 g2 Hg x. rewrite /= (Hg x) (Hf (g2 x)) //. Qed.

(* Function space maps *)
Definition ofe_mor_map {A A' B B'} (f : A' -n> A) (g : B -n> B')
  (h : A -n> B) : A' -n> B' := g ◎ h ◎ f.
Instance ofe_mor_map_ne {A A' B B'} n :
  Proper (dist n ==> dist n ==> dist n ==> dist n) (@ofe_mor_map A A' B B').
Proof. intros ??? ??? ???. by repeat apply ccompose_ne. Qed.

Definition ofe_morC_map {A A' B B'} (f : A' -n> A) (g : B -n> B') :
  (A -n> B) -n> (A' -n>  B') := CofeMor (ofe_mor_map f g).
Instance ofe_morC_map_ne {A A' B B'} :
  NonExpansive2 (@ofe_morC_map A A' B B').
Proof.
  intros n f f' Hf g g' Hg ?. rewrite /= /ofe_mor_map.
  by repeat apply ccompose_ne.
Qed.

(** unit *)
Section unit.
  Instance unit_dist : Dist unit := λ _ _ _, True.
  Definition unit_ofe_mixin : OfeMixin unit.
  Proof. by repeat split; try exists 0. Qed.
  Canonical Structure unitC : ofeT := OfeT unit unit_ofe_mixin.

  Global Program Instance unit_cofe : Cofe unitC := { compl x := () }.
  Next Obligation. by repeat split; try exists 0. Qed.

  Global Instance unit_ofe_discrete : OfeDiscrete unitC.
  Proof. done. Qed.
End unit.

(** Product *)
Section product.
  Context {A B : ofeT}.

  Instance prod_dist : Dist (A * B) := λ n, prod_relation (dist n) (dist n).
  Global Instance pair_ne :
    NonExpansive2 (@pair A B) := _.
  Global Instance fst_ne : NonExpansive (@fst A B) := _.
  Global Instance snd_ne : NonExpansive (@snd A B) := _.
  Definition prod_ofe_mixin : OfeMixin (A * B).
  Proof.
    split.
    - intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation.
      rewrite !equiv_dist; naive_solver.
    - apply _.
    - by intros n [x1 y1] [x2 y2] [??]; split; apply dist_S.
  Qed.
  Canonical Structure prodC : ofeT := OfeT (A * B) prod_ofe_mixin.

  Global Program Instance prod_cofe `{Cofe A, Cofe B} : Cofe prodC :=
    { compl c := (compl (chain_map fst c), compl (chain_map snd c)) }.
  Next Obligation.
    intros ?? n c; split. apply (conv_compl n (chain_map fst c)).
    apply (conv_compl n (chain_map snd c)).
  Qed.

  Global Instance prod_discrete (x : A * B) :
    Discrete (x.1) → Discrete (x.2) → Discrete x.
  Proof. by intros ???[??]; split; apply (discrete _). Qed.
  Global Instance prod_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete prodC.
  Proof. intros ?? [??]; apply _. Qed.
End product.

Arguments prodC : clear implicits.
Typeclasses Opaque prod_dist.

Instance prod_map_ne {A A' B B' : ofeT} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@prod_map A A' B B').
Proof. by intros f f' Hf g g' Hg ?? [??]; split; [apply Hf|apply Hg]. Qed.
Definition prodC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  prodC A B -n> prodC A' B' := CofeMor (prod_map f g).
Instance prodC_map_ne {A A' B B'} :
  NonExpansive2 (@prodC_map A A' B B').
Proof. intros n f f' Hf g g' Hg [??]; split; [apply Hf|apply Hg]. Qed.

(** Functors *)
Structure cFunctor := CFunctor {
  cFunctor_car : ofeT → ofeT → ofeT;
  cFunctor_map {A1 A2 B1 B2} :
    ((A2 -n> A1) * (B1 -n> B2)) → cFunctor_car A1 B1 -n> cFunctor_car A2 B2;
  cFunctor_ne {A1 A2 B1 B2} :
    NonExpansive (@cFunctor_map A1 A2 B1 B2);
  cFunctor_id {A B : ofeT} (x : cFunctor_car A B) :
    cFunctor_map (cid,cid) x ≡ x;
  cFunctor_compose {A1 A2 A3 B1 B2 B3}
      (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2) (g' : B2 -n> B3) x :
    cFunctor_map (f◎g, g'◎f') x ≡ cFunctor_map (g,g') (cFunctor_map (f,f') x)
}.
Existing Instance cFunctor_ne.
Instance: Params (@cFunctor_map) 5.

Delimit Scope cFunctor_scope with CF.
Bind Scope cFunctor_scope with cFunctor.

Class cFunctorContractive (F : cFunctor) :=
  cFunctor_contractive A1 A2 B1 B2 :> Contractive (@cFunctor_map F A1 A2 B1 B2).

Definition cFunctor_diag (F: cFunctor) (A: ofeT) : ofeT := cFunctor_car F A A.
Coercion cFunctor_diag : cFunctor >-> Funclass.

Program Definition constCF (B : ofeT) : cFunctor :=
  {| cFunctor_car A1 A2 := B; cFunctor_map A1 A2 B1 B2 f := cid |}.
Solve Obligations with done.
Coercion constCF : ofeT >-> cFunctor.

Instance constCF_contractive B : cFunctorContractive (constCF B).
Proof. rewrite /cFunctorContractive; apply _. Qed.

Program Definition idCF : cFunctor :=
  {| cFunctor_car A1 A2 := A2; cFunctor_map A1 A2 B1 B2 f := f.2 |}.
Solve Obligations with done.
Notation "∙" := idCF : cFunctor_scope.

Program Definition prodCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := prodC (cFunctor_car F1 A B) (cFunctor_car F2 A B);
  cFunctor_map A1 A2 B1 B2 fg :=
    prodC_map (cFunctor_map F1 fg) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply prodC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [??]; rewrite /= !cFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [??]; simpl.
  by rewrite !cFunctor_compose.
Qed.
Notation "F1 * F2" := (prodCF F1%CF F2%CF) : cFunctor_scope.

Instance prodCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (prodCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply prodC_map_ne; apply cFunctor_contractive.
Qed.

Program Definition ofe_morCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := cFunctor_car F1 B A -n> cFunctor_car F2 A B;
  cFunctor_map A1 A2 B1 B2 fg :=
    ofe_morC_map (cFunctor_map F1 (fg.2, fg.1)) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros F1 F2 A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morC_map_ne; apply cFunctor_ne; split; by apply Hfg.
Qed.
Next Obligation.
  intros F1 F2 A B [f ?] ?; simpl. rewrite /= !cFunctor_id.
  apply (ne_proper f). apply cFunctor_id.
Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [h ?] ?; simpl in *.
  rewrite -!cFunctor_compose. do 2 apply (ne_proper _). apply cFunctor_compose.
Qed.
Notation "F1 -n> F2" := (ofe_morCF F1%CF F2%CF) : cFunctor_scope.

Instance ofe_morCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (ofe_morCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n [f g] [f' g'] Hfg; simpl in *.
  apply ofe_morC_map_ne; apply cFunctor_contractive; destruct n, Hfg; by split.
Qed.

(** Sum *)
Section sum.
  Context {A B : ofeT}.

  Instance sum_dist : Dist (A + B) := λ n, sum_relation (dist n) (dist n).
  Global Instance inl_ne : NonExpansive (@inl A B) := _.
  Global Instance inr_ne : NonExpansive (@inr A B) := _.
  Global Instance inl_ne_inj : Inj (dist n) (dist n) (@inl A B) := _.
  Global Instance inr_ne_inj : Inj (dist n) (dist n) (@inr A B) := _.

  Definition sum_ofe_mixin : OfeMixin (A + B).
  Proof.
    split.
    - intros x y; split=> Hx.
      + destruct Hx=> n; constructor; by apply equiv_dist.
      + destruct (Hx 0); constructor; apply equiv_dist=> n; by apply (inj _).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure sumC : ofeT := OfeT (A + B) sum_ofe_mixin.

  Program Definition inl_chain (c : chain sumC) (a : A) : chain A :=
    {| chain_car n := match c n return _ with inl a' => a' | _ => a end |}.
  Next Obligation. intros c a n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Program Definition inr_chain (c : chain sumC) (b : B) : chain B :=
    {| chain_car n := match c n return _ with inr b' => b' | _ => b end |}.
  Next Obligation. intros c b n i ?; simpl. by destruct (chain_cauchy c n i). Qed.

  Definition sum_compl `{Cofe A, Cofe B} : Compl sumC := λ c,
    match c 0 with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.
  Global Program Instance sum_cofe `{Cofe A, Cofe B} : Cofe sumC :=
    { compl := sum_compl }.
  Next Obligation.
    intros ?? n c; rewrite /compl /sum_compl.
    feed inversion (chain_cauchy c 0 n); first by auto with lia; constructor.
    - rewrite (conv_compl n (inl_chain c _)) /=. destruct (c n); naive_solver.
    - rewrite (conv_compl n (inr_chain c _)) /=. destruct (c n); naive_solver.
  Qed.

  Global Instance inl_discrete (x : A) : Discrete x → Discrete (inl x).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance inr_discrete (y : B) : Discrete y → Discrete (inr y).
  Proof. inversion_clear 2; constructor; by apply (discrete _). Qed.
  Global Instance sum_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete sumC.
  Proof. intros ?? [?|?]; apply _. Qed.
End sum.

Arguments sumC : clear implicits.
Typeclasses Opaque sum_dist.

Instance sum_map_ne {A A' B B' : ofeT} n :
  Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==>
           dist n ==> dist n) (@sum_map A A' B B').
Proof.
  intros f f' Hf g g' Hg ??; destruct 1; constructor; [by apply Hf|by apply Hg].
Qed.
Definition sumC_map {A A' B B'} (f : A -n> A') (g : B -n> B') :
  sumC A B -n> sumC A' B' := CofeMor (sum_map f g).
Instance sumC_map_ne {A A' B B'} :
  NonExpansive2 (@sumC_map A A' B B').
Proof. intros n f f' Hf g g' Hg [?|?]; constructor; [apply Hf|apply Hg]. Qed.

Program Definition sumCF (F1 F2 : cFunctor) : cFunctor := {|
  cFunctor_car A B := sumC (cFunctor_car F1 A B) (cFunctor_car F2 A B);
  cFunctor_map A1 A2 B1 B2 fg :=
    sumC_map (cFunctor_map F1 fg) (cFunctor_map F2 fg)
|}.
Next Obligation.
  intros ?? A1 A2 B1 B2 n ???; by apply sumC_map_ne; apply cFunctor_ne.
Qed.
Next Obligation. by intros F1 F2 A B [?|?]; rewrite /= !cFunctor_id. Qed.
Next Obligation.
  intros F1 F2 A1 A2 A3 B1 B2 B3 f g f' g' [?|?]; simpl;
    by rewrite !cFunctor_compose.
Qed.
Notation "F1 + F2" := (sumCF F1%CF F2%CF) : cFunctor_scope.

Instance sumCF_contractive F1 F2 :
  cFunctorContractive F1 → cFunctorContractive F2 →
  cFunctorContractive (sumCF F1 F2).
Proof.
  intros ?? A1 A2 B1 B2 n ???;
    by apply sumC_map_ne; apply cFunctor_contractive.
Qed.

(** Discrete OFE *)
Section discrete_ofe.
  Context `{Equiv A} (Heq : @Equivalence A (≡)).

  Instance discrete_dist : Dist A := λ n x y, x ≡ y.
  Definition discrete_ofe_mixin : OfeMixin A.
  Proof using Type*.
    split.
    - intros x y; split; [done|intros Hn; apply (Hn 0)].
    - done.
    - done.
  Qed.

  Global Instance discrete_ofe_discrete : OfeDiscrete (OfeT A discrete_ofe_mixin).
  Proof. by intros x y. Qed.

  Global Program Instance discrete_cofe : Cofe (OfeT A discrete_ofe_mixin) :=
    { compl c := c 0 }.
  Next Obligation.
    intros n c. rewrite /compl /=;
    symmetry; apply (chain_cauchy c 0 n). omega.
  Qed.
End discrete_ofe.

Notation discreteC A := (OfeT A (discrete_ofe_mixin _)).
Notation leibnizC A := (OfeT A (@discrete_ofe_mixin _ equivL _)).

(** In order to define a discrete CMRA with carrier [A] (in the file [cmra.v])
we need to determine the [Equivalence A] proof that was used to construct the
OFE instance of [A] (note that this proof is not the same as the one we obtain
via [ofe_equivalence]).

We obtain the proof of [Equivalence A] by inferring the canonical OFE mixin
using [ofe_mixin_of A], and then check whether it is indeed a discrete OFE. This
will fail if no OFE, or an OFE other than the discrete OFE, was registered. *)
Notation discrete_ofe_equivalence_of A := ltac:(
  match constr:(ofe_mixin_of A) with
  | discrete_ofe_mixin ?H => exact H
  end) (only parsing).

Instance leibnizC_leibniz A : LeibnizEquiv (leibnizC A).
Proof. by intros x y. Qed.

Canonical Structure boolC := leibnizC bool.
Canonical Structure natC := leibnizC nat.
Canonical Structure positiveC := leibnizC positive.
Canonical Structure NC := leibnizC N.
Canonical Structure ZC := leibnizC Z.

(* Option *)
Section option.
  Context {A : ofeT}.

  Instance option_dist : Dist (option A) := λ n, option_Forall2 (dist n).
  Lemma dist_option_Forall2 n mx my : mx ≡{n}≡ my ↔ option_Forall2 (dist n) mx my.
  Proof. done. Qed.

  Definition option_ofe_mixin : OfeMixin (option A).
  Proof.
    split.
    - intros mx my; split; [by destruct 1; constructor; apply equiv_dist|].
      intros Hxy; destruct (Hxy 0); constructor; apply equiv_dist.
      by intros n; feed inversion (Hxy n).
    - apply _.
    - destruct 1; constructor; by apply dist_S.
  Qed.
  Canonical Structure optionC := OfeT (option A) option_ofe_mixin.

  Program Definition option_chain (c : chain optionC) (x : A) : chain A :=
    {| chain_car n := from_option id x (c n) |}.
  Next Obligation. intros c x n i ?; simpl. by destruct (chain_cauchy c n i). Qed.
  Definition option_compl `{Cofe A} : Compl optionC := λ c,
    match c 0 with Some x => Some (compl (option_chain c x)) | None => None end.
  Global Program Instance option_cofe `{Cofe A} : Cofe optionC :=
    { compl := option_compl }.
  Next Obligation.
    intros ? n c; rewrite /compl /option_compl.
    feed inversion (chain_cauchy c 0 n); auto with lia; [].
    constructor. rewrite (conv_compl n (option_chain c _)) /=.
    destruct (c n); naive_solver.
  Qed.

  Global Instance option_ofe_discrete : OfeDiscrete A → OfeDiscrete optionC.
  Proof. destruct 2; constructor; by apply (discrete _). Qed.

  Global Instance Some_ne : NonExpansive (@Some A).
  Proof. by constructor. Qed.
  Global Instance is_Some_ne n : Proper (dist n ==> iff) (@is_Some A).
  Proof. destruct 1; split; eauto. Qed.
  Global Instance Some_dist_inj : Inj (dist n) (dist n) (@Some A).
  Proof. by inversion_clear 1. Qed.
  Global Instance from_option_ne {B} (R : relation B) (f : A → B) n :
    Proper (dist n ==> R) f → Proper (R ==> dist n ==> R) (from_option f).
  Proof. destruct 3; simpl; auto. Qed.

  Global Instance None_discrete : Discrete (@None A).
  Proof. inversion_clear 1; constructor. Qed.
  Global Instance Some_discrete x : Discrete x → Discrete (Some x).
  Proof. by intros ?; inversion_clear 1; constructor; apply discrete. Qed.

  Lemma dist_None n mx : mx ≡{n}≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|by intros ->]. Qed.
  Lemma dist_Some_inv_l n mx my x :
    mx ≡{n}≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_r n mx my y :
    mx ≡{n}≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡{n}≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma dist_Some_inv_l' n my x : Some x ≡{n}≡ my → ∃ x', Some x' = my ∧ x ≡{n}≡ x'.
  Proof. intros ?%(dist_Some_inv_l _ _ _ x); naive_solver. Qed.
  Lemma dist_Some_inv_r' n mx y : mx ≡{n}≡ Some y → ∃ y', mx = Some y' ∧ y ≡{n}≡ y'.
  Proof. intros ?%(dist_Some_inv_r _ _ _ y); naive_solver. Qed.
End option.

Typeclasses Opaque option_dist.
Arguments optionC : clear implicits.

Instance option_fmap_ne {A B : ofeT} n:
  Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap option _ A B).
Proof. intros f f' Hf ?? []; constructor; auto. Qed.
Definition optionC_map {A B} (f : A -n> B) : optionC A -n> optionC B :=
  CofeMor (fmap f : optionC A → optionC B).
Instance optionC_map_ne A B : NonExpansive (@optionC_map A B).
Proof. by intros n f f' Hf []; constructor; apply Hf. Qed.

Program Definition optionCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := optionC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := optionC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(option_fmap_id x).
  apply option_fmap_equiv_ext=>y; apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -option_fmap_compose.
  apply option_fmap_equiv_ext=>y; apply cFunctor_compose.
Qed.

Instance optionCF_contractive F :
  cFunctorContractive F → cFunctorContractive (optionCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply optionC_map_ne, cFunctor_contractive.
Qed.

(** Later *)
Inductive later (A : Type) : Type := Next { later_car : A }.
Add Printing Constructor later.
Arguments Next {_} _.
Arguments later_car {_} _.
Instance: Params (@Next) 1.

Section later.
  Context {A : ofeT}.
  Instance later_equiv : Equiv (later A) := λ x y, later_car x ≡ later_car y.
  Instance later_dist : Dist (later A) := λ n x y,
    dist_later n (later_car x) (later_car y).
  Definition later_ofe_mixin : OfeMixin (later A).
  Proof.
    split.
    - intros x y; unfold equiv, later_equiv; rewrite !equiv_dist.
      split. intros Hxy [|n]; [done|apply Hxy]. intros Hxy n; apply (Hxy (S n)).
    - split; rewrite /dist /later_dist.
      + by intros [x].
      + by intros [x] [y].
      + by intros [x] [y] [z] ??; trans y.
    - intros [|n] [x] [y] ?; [done|]; rewrite /dist /later_dist; by apply dist_S.
  Qed.
  Canonical Structure laterC : ofeT := OfeT (later A) later_ofe_mixin.

  Program Definition later_chain (c : chain laterC) : chain A :=
    {| chain_car n := later_car (c (S n)) |}.
  Next Obligation. intros c n i ?; apply (chain_cauchy c (S n)); lia. Qed.
  Global Program Instance later_cofe `{Cofe A} : Cofe laterC :=
    { compl c := Next (compl (later_chain c)) }.
  Next Obligation.
    intros ? [|n] c; [done|by apply (conv_compl n (later_chain c))].
  Qed.

  Global Instance Next_contractive : Contractive (@Next A).
  Proof. by intros [|n] x y. Qed.
  Global Instance Later_inj n : Inj (dist n) (dist (S n)) (@Next A).
  Proof. by intros x y. Qed.

  Instance later_car_anti_contractive n :
    Proper (dist n ==> dist_later n) later_car.
  Proof. move=> [x] [y] /= Hxy. done. Qed.

  (* f is contractive iff it can factor into `Next` and a non-expansive function. *)
  Lemma contractive_alt {B : ofeT} (f : A → B) :
    Contractive f ↔ ∃ g : later A → B, NonExpansive g ∧ ∀ x, f x ≡ g (Next x).
  Proof.
    split.
    - intros Hf. exists (f ∘ later_car); split=> // n x y ?. by f_equiv.
    - intros (g&Hg&Hf) n x y Hxy. rewrite !Hf. by apply Hg.
  Qed.
End later.

Arguments laterC : clear implicits.

Definition later_map {A B} (f : A → B) (x : later A) : later B :=
  Next (f (later_car x)).
Instance later_map_ne {A B : ofeT} (f : A → B) n :
  Proper (dist (pred n) ==> dist (pred n)) f →
  Proper (dist n ==> dist n) (later_map f) | 0.
Proof. destruct n as [|n]; intros Hf [x] [y] ?; do 2 red; simpl; auto. Qed.
Lemma later_map_id {A} (x : later A) : later_map id x = x.
Proof. by destruct x. Qed.
Lemma later_map_compose {A B C} (f : A → B) (g : B → C) (x : later A) :
  later_map (g ∘ f) x = later_map g (later_map f x).
Proof. by destruct x. Qed.
Lemma later_map_ext {A B : ofeT} (f g : A → B) x :
  (∀ x, f x ≡ g x) → later_map f x ≡ later_map g x.
Proof. destruct x; intros Hf; apply Hf. Qed.
Definition laterC_map {A B} (f : A -n> B) : laterC A -n> laterC B :=
  CofeMor (later_map f).
Instance laterC_map_contractive (A B : ofeT) : Contractive (@laterC_map A B).
Proof. intros [|n] f g Hf n'; [done|]; apply Hf; lia. Qed.

Program Definition laterCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := laterC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := laterC_map (cFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 A2 B1 B2 n fg fg' ?.
  by apply (contractive_ne laterC_map), cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x; simpl. rewrite -{2}(later_map_id x).
  apply later_map_ext=>y. by rewrite cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x; simpl. rewrite -later_map_compose.
  apply later_map_ext=>y; apply cFunctor_compose.
Qed.
Notation "▶ F"  := (laterCF F%CF) (at level 20, right associativity) : cFunctor_scope.

Instance laterCF_contractive F : cFunctorContractive (laterCF F).
Proof.
  intros A1 A2 B1 B2 n fg fg' Hfg. apply laterC_map_contractive.
  destruct n as [|n]; simpl in *; first done. apply cFunctor_ne, Hfg.
Qed.

(* Dependently-typed functions over a discrete domain *)
(* We make [ofe_fun] a definition so that we can register it as a canonical
structure. *)
Definition ofe_fun {A} (B : A → ofeT) := ∀ x : A, B x.

Section ofe_fun.
  Context {A : Type} {B : A → ofeT}.
  Implicit Types f g : ofe_fun B.

  Instance ofe_fun_equiv : Equiv (ofe_fun B) := λ f g, ∀ x, f x ≡ g x.
  Instance ofe_fun_dist : Dist (ofe_fun B) := λ n f g, ∀ x, f x ≡{n}≡ g x.
  Definition ofe_fun_ofe_mixin : OfeMixin (ofe_fun B).
  Proof.
    split.
    - intros f g; split; [intros Hfg n k; apply equiv_dist, Hfg|].
      intros Hfg k; apply equiv_dist=> n; apply Hfg.
    - intros n; split.
      + by intros f x.
      + by intros f g ? x.
      + by intros f g h ?? x; trans (g x).
    - by intros n f g ? x; apply dist_S.
  Qed.
  Canonical Structure ofe_funC := OfeT (ofe_fun B) ofe_fun_ofe_mixin.

  Program Definition ofe_fun_chain `(c : chain ofe_funC)
    (x : A) : chain (B x) := {| chain_car n := c n x |}.
  Next Obligation. intros c x n i ?. by apply (chain_cauchy c). Qed.
  Global Program Instance ofe_fun_cofe `{∀ x, Cofe (B x)} : Cofe ofe_funC :=
    { compl c x := compl (ofe_fun_chain c x) }.
  Next Obligation. intros ? n c x. apply (conv_compl n (ofe_fun_chain c x)). Qed.

  Global Instance ofe_fun_inhabited `{∀ x, Inhabited (B x)} : Inhabited ofe_funC :=
    populate (λ _, inhabitant).
  Global Instance ofe_fun_lookup_discrete `{EqDecision A} f x :
    Discrete f → Discrete (f x).
  Proof.
    intros Hf y ?.
    set (g x' := if decide (x = x') is left H then eq_rect _ B y _ H else f x').
    trans (g x).
    { apply Hf=> x'. unfold g. by destruct (decide _) as [[]|]. }
    unfold g. destruct (decide _) as [Hx|]; last done.
    by rewrite (proof_irrel Hx eq_refl).
  Qed.
End ofe_fun.

Arguments ofe_funC {_} _.
Notation "A -c> B" :=
  (@ofe_funC A (λ _, B)) (at level 99, B at level 200, right associativity).

Definition ofe_fun_map {A} {B1 B2 : A → ofeT} (f : ∀ x, B1 x → B2 x)
  (g : ofe_fun B1) : ofe_fun B2 := λ x, f _ (g x).

Lemma ofe_fun_map_ext {A} {B1 B2 : A → ofeT} (f1 f2 : ∀ x, B1 x → B2 x)
  (g : ofe_fun B1) :
  (∀ x, f1 x (g x) ≡ f2 x (g x)) → ofe_fun_map f1 g ≡ ofe_fun_map f2 g.
Proof. done. Qed.
Lemma ofe_fun_map_id {A} {B : A → ofeT} (g : ofe_fun B) :
  ofe_fun_map (λ _, id) g = g.
Proof. done. Qed.
Lemma ofe_fun_map_compose {A} {B1 B2 B3 : A → ofeT}
    (f1 : ∀ x, B1 x → B2 x) (f2 : ∀ x, B2 x → B3 x) (g : ofe_fun B1) :
  ofe_fun_map (λ x, f2 x ∘ f1 x) g = ofe_fun_map f2 (ofe_fun_map f1 g).
Proof. done. Qed.

Instance ofe_fun_map_ne {A} {B1 B2 : A → ofeT} (f : ∀ x, B1 x → B2 x) n :
  (∀ x, Proper (dist n ==> dist n) (f x)) →
  Proper (dist n ==> dist n) (ofe_fun_map f).
Proof. by intros ? y1 y2 Hy x; rewrite /ofe_fun_map (Hy x). Qed.

Definition ofe_funC_map {A} {B1 B2 : A → ofeT} (f : ofe_fun (λ x, B1 x -n> B2 x)) :
  ofe_funC B1 -n> ofe_funC B2 := CofeMor (ofe_fun_map f).
Instance ofe_funC_map_ne {A} {B1 B2 : A → ofeT} :
  NonExpansive (@ofe_funC_map A B1 B2).
Proof. intros n f1 f2 Hf g x; apply Hf. Qed.

Program Definition ofe_funCF {C} (F : C → cFunctor) : cFunctor := {|
  cFunctor_car A B := ofe_funC (λ c, cFunctor_car (F c) A B);
  cFunctor_map A1 A2 B1 B2 fg := ofe_funC_map (λ c, cFunctor_map (F c) fg)
|}.
Next Obligation.
  intros C F A1 A2 B1 B2 n ?? g. by apply ofe_funC_map_ne=>?; apply cFunctor_ne.
Qed.
Next Obligation.
  intros C F A B g; simpl. rewrite -{2}(ofe_fun_map_id g).
  apply ofe_fun_map_ext=> y; apply cFunctor_id.
Qed.
Next Obligation.
  intros C F A1 A2 A3 B1 B2 B3 f1 f2 f1' f2' g. rewrite /= -ofe_fun_map_compose.
  apply ofe_fun_map_ext=>y; apply cFunctor_compose.
Qed.

Notation "T -c> F" := (@ofe_funCF T%type (λ _, F%CF)) : cFunctor_scope.

Instance ofe_funCF_contractive {C} (F : C → cFunctor) :
  (∀ c, cFunctorContractive (F c)) → cFunctorContractive (ofe_funCF F).
Proof.
  intros ? A1 A2 B1 B2 n ?? g.
  by apply ofe_funC_map_ne=>c; apply cFunctor_contractive.
Qed.

(** Constructing isomorphic OFEs *)
Lemma iso_ofe_mixin {A : ofeT} `{Equiv B, Dist B} (g : B → A)
  (g_equiv : ∀ y1 y2, y1 ≡ y2 ↔ g y1 ≡ g y2)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2) : OfeMixin B.
Proof.
  split.
  - intros y1 y2. rewrite g_equiv. setoid_rewrite g_dist. apply equiv_dist.
  - split.
    + intros y. by apply g_dist.
    + intros y1 y2. by rewrite !g_dist.
    + intros y1 y2 y3. rewrite !g_dist. intros ??; etrans; eauto.
  - intros n y1 y2. rewrite !g_dist. apply dist_S.
Qed.

Section iso_cofe_subtype.
  Context {A B : ofeT} `{Cofe A} (P : A → Prop) (f : ∀ x, P x → B) (g : B → A).
  Context (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2).
  Let Hgne : NonExpansive g.
  Proof. intros n y1 y2. apply g_dist. Qed.
  Existing Instance Hgne.
  Context (gf : ∀ x Hx, g (f x Hx) ≡ x).
  Context (Hlimit : ∀ c : chain B, P (compl (chain_map g c))).
  Program Definition iso_cofe_subtype : Cofe B :=
    {| compl c := f (compl (chain_map g c)) _ |}.
  Next Obligation. apply Hlimit. Qed.
  Next Obligation.
    intros n c; simpl. apply g_dist. by rewrite gf conv_compl.
  Qed.
End iso_cofe_subtype.

Lemma iso_cofe_subtype' {A B : ofeT} `{Cofe A}
  (P : A → Prop) (f : ∀ x, P x → B) (g : B → A)
  (Pg : ∀ y, P (g y))
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x Hx, g (f x Hx) ≡ x)
  (Hlimit : LimitPreserving P) : Cofe B.
Proof. apply: (iso_cofe_subtype P f g)=> // c. apply Hlimit=> ?; apply Pg. Qed.

Definition iso_cofe {A B : ofeT} `{Cofe A} (f : A → B) (g : B → A)
  (g_dist : ∀ n y1 y2, y1 ≡{n}≡ y2 ↔ g y1 ≡{n}≡ g y2)
  (gf : ∀ x, g (f x) ≡ x) : Cofe B.
Proof. by apply (iso_cofe_subtype (λ _, True) (λ x _, f x) g). Qed.

(** Sigma *)
Section sigma.
  Context {A : ofeT} {P : A → Prop}.
  Implicit Types x : sig P.

  (* TODO: Find a better place for this Equiv instance. It also
     should not depend on A being an OFE. *)
  Instance sig_equiv : Equiv (sig P) := λ x1 x2, `x1 ≡ `x2.
  Instance sig_dist : Dist (sig P) := λ n x1 x2, `x1 ≡{n}≡ `x2.

  Definition sig_equiv_alt x y : x ≡ y ↔ `x ≡ `y := reflexivity _.
  Definition sig_dist_alt n x y : x ≡{n}≡ y ↔ `x ≡{n}≡ `y := reflexivity _.

  Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
    a1 ≡{n}≡ a2 → a1 ↾ H1 ≡{n}≡ a2 ↾ H2.
  Proof. done. Qed.

  Global Instance proj1_sig_ne : NonExpansive (@proj1_sig _ P).
  Proof. by intros n [a Ha] [b Hb] ?. Qed.
  Definition sig_ofe_mixin : OfeMixin (sig P).
  Proof. by apply (iso_ofe_mixin proj1_sig). Qed.
  Canonical Structure sigC : ofeT := OfeT (sig P) sig_ofe_mixin.

  Global Instance sig_cofe `{Cofe A, !LimitPreserving P} : Cofe sigC.
  Proof. apply (iso_cofe_subtype' P (exist P) proj1_sig)=> //. by intros []. Qed.

  Global Instance sig_discrete (x : sig P) :  Discrete (`x) → Discrete x.
  Proof. intros ? y. rewrite sig_dist_alt sig_equiv_alt. apply (discrete _). Qed.
  Global Instance sig_ofe_discrete : OfeDiscrete A → OfeDiscrete sigC.
  Proof. intros ??. apply _. Qed.
End sigma.

Arguments sigC {_} _.
