From iris.algebra Require Export ofe.
Set Default Proof Using "Type".

(** The Monoid class that is used for generic big operators in the file
[algebra/big_op]. The operation is an argument because we want to have multiple
monoids over the same type (for example, on [uPred]s we have monoids for [∗],
[∧], and [∨]). However, we do bundle the unit because:

- If we would not, it would appear explicitly in an argument of the big
  operators, which confuses rewrite. Now it is hidden in the class, and hence
  rewrite won't even see it.
- The unit is unique.

We could in principle have big ops over setoids instead of OFEs. However, since
we do not have a canonical structure for setoids, we do not go that way.

Note that we do not declare any of the projections as type class instances. That
is because we only need them in the [big_op] file, and nowhere else. Hence, we
declare these instances locally there to avoid them being used elsewhere. *)
Class Monoid {M : ofeT} (o : M → M → M) := {
  monoid_unit : M;
  monoid_ne : NonExpansive2 o;
  monoid_assoc : Assoc (≡) o;
  monoid_comm : Comm (≡) o;
  monoid_left_id : LeftId (≡) monoid_unit o;
}.
Lemma monoid_proper `{Monoid M o} : Proper ((≡) ==> (≡) ==> (≡)) o.
Proof. apply ne_proper_2, monoid_ne. Qed.
Lemma monoid_right_id `{Monoid M o} : RightId (≡) monoid_unit o.
Proof. intros x. etrans; [apply monoid_comm|apply monoid_left_id]. Qed.

(** The [Homomorphism] classes give rise to generic lemmas about big operators
commuting with each other. We also consider a [WeakMonoidHomomorphism] which
does not necesarrily commute with unit; an example is the [own] connective: we
only have `True ==∗ own γ ∅`, not `True ↔ own γ ∅`. *)
Class WeakMonoidHomomorphism {M1 M2 : ofeT}
    (o1 : M1 → M1 → M1) (o2 : M2 → M2 → M2) `{Monoid M1 o1, Monoid M2 o2}
    (R : relation M2) (f : M1 → M2) := {
  monoid_homomorphism_rel_po : PreOrder R;
  monoid_homomorphism_rel_proper : Proper ((≡) ==> (≡) ==> iff) R;
  monoid_homomorphism_op_proper : Proper (R ==> R ==> R) o2;
  monoid_homomorphism_ne : NonExpansive f;
  monoid_homomorphism x y : R (f (o1 x y)) (o2 (f x) (f y))
}.

Class MonoidHomomorphism {M1 M2 : ofeT}
    (o1 : M1 → M1 → M1) (o2 : M2 → M2 → M2) `{Monoid M1 o1, Monoid M2 o2}
    (R : relation M2) (f : M1 → M2) := {
  monoid_homomorphism_weak :> WeakMonoidHomomorphism o1 o2 R f;
  monoid_homomorphism_unit : R (f monoid_unit) monoid_unit
}.

Lemma weak_monoid_homomorphism_proper
  `{WeakMonoidHomomorphism M1 M2 o1 o2 R f} : Proper ((≡) ==> (≡)) f.
Proof. apply ne_proper, monoid_homomorphism_ne. Qed.
