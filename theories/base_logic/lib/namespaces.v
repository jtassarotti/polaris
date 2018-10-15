From stdpp Require Export countable coPset.
From iris.algebra Require Export base.
Set Default Proof Using "Type".

Definition namespace := list positive.
Instance namespace_eq_dec : EqDecision namespace := _.
Instance namespace_countable : Countable namespace := _.
Typeclasses Opaque namespace.

Definition nroot : namespace := nil.

Definition ndot_def `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Definition ndot_aux : seal (@ndot_def). by eexists. Qed.
Definition ndot {A A_dec A_count}:= unseal ndot_aux A A_dec A_count.
Definition ndot_eq : @ndot = @ndot_def := seal_eq ndot_aux.

Definition nclose_def (N : namespace) : coPset := coPset_suffixes (encode N).
Definition nclose_aux : seal (@nclose_def). by eexists. Qed.
Instance nclose : UpClose namespace coPset := unseal nclose_aux.
Definition nclose_eq : @nclose = @nclose_def := seal_eq nclose_aux.

Notation "N .@ x" := (ndot N x)
  (at level 19, left associativity, format "N .@ x") : stdpp_scope.
Notation "(.@)" := ndot (only parsing) : stdpp_scope.

Instance ndisjoint : Disjoint namespace := λ N1 N2, nclose N1 ## nclose N2.

Section namespace.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types N : namespace.
  Implicit Types E : coPset.

  Global Instance ndot_inj : Inj2 (=) (=) (=) (@ndot A _ _).
  Proof. intros N1 x1 N2 x2; rewrite !ndot_eq=> ?; by simplify_eq. Qed.

  Lemma nclose_nroot : ↑nroot = (⊤:coPset).
  Proof. rewrite nclose_eq. by apply (sig_eq_pi _). Qed.
  Lemma encode_nclose N : encode N ∈ (↑N:coPset).
  Proof.
    rewrite nclose_eq.
    by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _).
  Qed.

  Lemma nclose_subseteq N x : ↑N.@x ⊆ (↑N : coPset).
  Proof.
    intros p; rewrite nclose_eq /nclose !ndot_eq !elem_coPset_suffixes.
    intros [q ->]. destruct (list_encode_suffix N (ndot_def N x)) as [q' ?].
    { by exists [encode x]. }
    by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
  Qed.

  Lemma nclose_subseteq' E N x : ↑N ⊆ E → ↑N.@x ⊆ E.
  Proof. intros. etrans; eauto using nclose_subseteq. Qed.

  Lemma ndot_nclose N x : encode (N.@x) ∈ (↑N:coPset).
  Proof. apply nclose_subseteq with x, encode_nclose. Qed.
  Lemma nclose_infinite N : ¬set_finite (↑ N : coPset).
  Proof. rewrite nclose_eq. apply coPset_suffixes_infinite. Qed.

  Lemma ndot_ne_disjoint N x y : x ≠ y → N.@x ## N.@y.
  Proof.
    intros Hxy a. rewrite !nclose_eq !elem_coPset_suffixes !ndot_eq.
    intros [qx ->] [qy Hqy].
    revert Hqy. by intros [= ?%encode_inj]%list_encode_suffix_eq.
  Qed.

  Lemma ndot_preserve_disjoint_l N E x : ↑N ## E → ↑N.@x ## E.
  Proof. intros. pose proof (nclose_subseteq N x). set_solver. Qed.

  Lemma ndot_preserve_disjoint_r N E x : E ## ↑N → E ## ↑N.@x.
  Proof. intros. by apply symmetry, ndot_preserve_disjoint_l. Qed.

  Lemma ndisj_subseteq_difference N E F : E ## ↑N → E ⊆ F → E ⊆ F ∖ ↑N.
  Proof. set_solver. Qed.

  Lemma namespace_subseteq_difference_l E1 E2 E3 : E1 ⊆ E3 → E1 ∖ E2 ⊆ E3.
  Proof. set_solver. Qed.

  Lemma ndisj_difference_l E N1 N2 : ↑N2 ⊆ (↑N1 : coPset) → E ∖ ↑N1 ## ↑N2.
  Proof. set_solver. Qed.
End namespace.

(* The hope is that registering these will suffice to solve most goals
of the forms:
- [N1 ## N2] 
- [↑N1 ⊆ E ∖ ↑N2 ∖ .. ∖ ↑Nn]
- [E1 ∖ ↑N1 ⊆ E2 ∖ ↑N2 ∖ .. ∖ ↑Nn] *)
Create HintDb ndisj.
Hint Resolve ndisj_subseteq_difference : ndisj.
Hint Extern 0 (_ ## _) => apply ndot_ne_disjoint; congruence : ndisj.
Hint Resolve ndot_preserve_disjoint_l ndot_preserve_disjoint_r : ndisj.
Hint Resolve nclose_subseteq' ndisj_difference_l : ndisj.
Hint Resolve namespace_subseteq_difference_l | 100 : ndisj.
Hint Resolve (empty_subseteq (A:=positive) (C:=coPset)) : ndisj.
Hint Resolve (union_least (A:=positive) (C:=coPset)) : ndisj.

Ltac solve_ndisj :=
  repeat match goal with
  | H : _ ∪ _ ⊆ _ |- _ => apply union_subseteq in H as [??]
  end;
  solve [eauto with ndisj].
Hint Extern 1000 => solve_ndisj : solve_ndisj.
