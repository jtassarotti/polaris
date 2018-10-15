From stdpp Require Export strings.
From iris.algebra Require Export base.
From Coq Require Import Ascii.
Set Default Proof Using "Type".

(* Directions of rewrites *)
Inductive direction := Left | Right.

(* Some specific versions of operations on strings for the proof mode. We need
those so that we can make [cbv] unfold just them, but not the actual operations
that may appear in users' proofs. *)
Local Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.

Lemma lazy_andb_true (b1 b2 : bool) : b1 && b2 = true ↔ b1 = true ∧ b2 = true.
Proof. destruct b1, b2; intuition congruence. Qed.

Definition beq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false | true, true => true
  | _, _ => false
  end.

Definition ascii_beq (x y : ascii) : bool :=
  let 'Ascii x1 x2 x3 x4 x5 x6 x7 x8 := x in
  let 'Ascii y1 y2 y3 y4 y5 y6 y7 y8 := y in
  beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4 &&
    beq x5 y5 && beq x6 y6 && beq x7 y7 && beq x8 y8.

Fixpoint string_beq (s1 s2 : string) : bool :=
  match s1, s2 with 
  | "", "" => true
  | String a1 s1, String a2 s2 => ascii_beq a1 a2 && string_beq s1 s2
  | _, _ => false
  end.

Lemma beq_true b1 b2 : beq b1 b2 = true ↔ b1 = b2.
Proof. destruct b1, b2; simpl; intuition congruence. Qed.

Lemma ascii_beq_true x y : ascii_beq x y = true ↔ x = y.
Proof.
  destruct x, y; rewrite /= !lazy_andb_true !beq_true. intuition congruence.
Qed.

Lemma string_beq_true s1 s2 : string_beq s1 s2 = true ↔ s1 = s2.
Proof.
  revert s2. induction s1 as [|x s1 IH]=> -[|y s2] //=.
  rewrite lazy_andb_true ascii_beq_true IH. intuition congruence.
Qed.

Lemma string_beq_reflect s1 s2 : reflect (s1 = s2) (string_beq s1 s2).
Proof. apply iff_reflect. by rewrite string_beq_true. Qed.

Module Export ident.
Inductive ident :=
  | IAnon : positive → ident
  | INamed :> string → ident.
End ident.

Instance maybe_IAnon : Maybe IAnon := λ i,
  match i with IAnon n => Some n | _ => None end.
Instance maybe_INamed : Maybe INamed := λ i,
  match i with INamed s => Some s | _ => None end.

Instance beq_eq_dec : EqDecision ident.
Proof. solve_decision. Defined.

Definition positive_beq := Eval compute in Pos.eqb.

Lemma positive_beq_true x y : positive_beq x y = true ↔ x = y.
Proof. apply Pos.eqb_eq. Qed.

Definition ident_beq (i1 i2 : ident) : bool :=
  match i1, i2 with
  | IAnon n1, IAnon n2 => positive_beq n1 n2
  | INamed s1, INamed s2 => string_beq s1 s2
  | _, _ => false
  end.

Lemma ident_beq_true i1 i2 : ident_beq i1 i2 = true ↔ i1 = i2.
Proof.
  destruct i1, i2; rewrite /= ?string_beq_true ?positive_beq_true; naive_solver.
Qed.

Lemma ident_beq_reflect i1 i2 : reflect (i1 = i2) (ident_beq i1 i2).
Proof. apply iff_reflect. by rewrite ident_beq_true. Qed.

Definition option_bind {A B} (f : A → option B) (mx : option A) : option B :=
  match mx with Some x => f x | None => None end.
Arguments option_bind _ _ _ !_ /.
