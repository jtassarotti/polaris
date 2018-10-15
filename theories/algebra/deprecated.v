From iris.algebra Require Import ofe cmra.
Set Default Proof Using "Type".

(* Old notation for backwards compatibility. *)

(* Deprecated 2016-11-22. Use ofeT instead. *)
Notation cofeT := ofeT (only parsing).

(* Deprecated 2016-12-09. Use agree instead. *)
Module dec_agree.
Local Arguments validN _ _ _ !_ /.
Local Arguments valid _ _  !_ /.
Local Arguments op _ _ _ !_ /.
Local Arguments pcore _ _ !_ /.

(* This is isomorphic to option, but has a very different RA structure. *)
Inductive dec_agree (A : Type) : Type := 
  | DecAgree : A → dec_agree A
  | DecAgreeBot : dec_agree A.
Arguments DecAgree {_} _.
Arguments DecAgreeBot {_}.
Instance maybe_DecAgree {A} : Maybe (@DecAgree A) := λ x,
  match x with DecAgree a => Some a | _ => None end.

Section dec_agree.
Context `{EqDecision A}.
Implicit Types a b : A.
Implicit Types x y : dec_agree A.

Instance dec_agree_valid : Valid (dec_agree A) := λ x,
  if x is DecAgree _ then True else False.
Canonical Structure dec_agreeC : ofeT := leibnizC (dec_agree A).

Instance dec_agree_op : Op (dec_agree A) := λ x y,
  match x, y with
  | DecAgree a, DecAgree b => if decide (a = b) then DecAgree a else DecAgreeBot
  | _, _ => DecAgreeBot
  end.
Instance dec_agree_pcore : PCore (dec_agree A) := Some.

Definition dec_agree_ra_mixin : RAMixin (dec_agree A).
Proof.
  apply ra_total_mixin; apply _ || eauto.
  - intros [?|] [?|] [?|]; by repeat (simplify_eq/= || case_match).
  - intros [?|] [?|]; by repeat (simplify_eq/= || case_match).
  - intros [?|]; by repeat (simplify_eq/= || case_match).
  - by intros [?|] [?|] ?.
Qed.

Canonical Structure dec_agreeR : cmraT :=
  discreteR (dec_agree A) dec_agree_ra_mixin.

Global Instance dec_agree_cmra_discrete : CmraDiscrete dec_agreeR.
Proof. apply discrete_cmra_discrete. Qed.
Global Instance dec_agree_cmra_total : CmraTotal dec_agreeR.
Proof. intros x. by exists x. Qed.

(* Some properties of this CMRA *)
Global Instance dec_agree_core_id (x : dec_agreeR) : CoreId x.
Proof. by constructor. Qed.

Lemma dec_agree_ne a b : a ≠ b → DecAgree a ⋅ DecAgree b = DecAgreeBot.
Proof. intros. by rewrite /= decide_False. Qed.

Lemma dec_agree_idemp (x : dec_agree A) : x ⋅ x = x.
Proof. destruct x; by rewrite /= ?decide_True. Qed.

Lemma dec_agree_op_inv (x1 x2 : dec_agree A) : ✓ (x1 ⋅ x2) → x1 = x2.
Proof. destruct x1, x2; by repeat (simplify_eq/= || case_match). Qed.

Lemma DecAgree_included a b : DecAgree a ≼ DecAgree b ↔ a = b.
Proof.
  split. intros [[c|] [=]%leibniz_equiv]. by simplify_option_eq. by intros ->.
Qed.
End dec_agree.

Arguments dec_agreeC : clear implicits.
Arguments dec_agreeR _ {_}.
End dec_agree.
