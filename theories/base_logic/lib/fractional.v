From stdpp Require Import gmap gmultiset.
From iris.base_logic Require Export derived.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import classes class_instances.
Set Default Proof Using "Type".

Class Fractional {M} (Φ : Qp → uPred M) :=
  fractional p q : Φ (p + q)%Qp ⊣⊢ Φ p ∗ Φ q.
Class AsFractional {M} (P : uPred M) (Φ : Qp → uPred M) (q : Qp) := {
  as_fractional : P ⊣⊢ Φ q;
  as_fractional_fractional :> Fractional Φ
}.

Arguments fractional {_ _ _} _ _.

Hint Mode AsFractional - + - - : typeclass_instances.
Hint Mode AsFractional - - + + : typeclass_instances.

Section fractional.
  Context {M : ucmraT}.
  Implicit Types P Q : uPred M.
  Implicit Types Φ : Qp → uPred M.
  Implicit Types q : Qp.

  Lemma fractional_split P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P ⊣⊢ P1 ∗ P2.
  Proof. by move=>-[-> ->] [-> _] [-> _]. Qed.
  Lemma fractional_split_1 P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P -∗ P1 ∗ P2.
  Proof. intros. by rewrite -fractional_split. Qed.
  Lemma fractional_split_2 P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    P1 -∗ P2 -∗ P.
  Proof. intros. apply uPred.wand_intro_r. by rewrite -fractional_split. Qed.

  Lemma fractional_half P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P ⊣⊢ P12 ∗ P12.
  Proof. by rewrite -{1}(Qp_div_2 q)=>-[->->][-> _]. Qed.
  Lemma fractional_half_1 P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P -∗ P12 ∗ P12.
  Proof. intros. by rewrite -fractional_half. Qed.
  Lemma fractional_half_2 P P12 Φ q :
    AsFractional P Φ q → AsFractional P12 Φ (q/2) →
    P12 -∗ P12 -∗ P.
  Proof. intros. apply uPred.wand_intro_r. by rewrite -fractional_half. Qed.

  (** Fractional and logical connectives *)
  Global Instance persistent_fractional P :
    Persistent P → Fractional (λ _, P).
  Proof. intros HP q q'. by apply uPred.sep_dup. Qed.

  Global Instance fractional_sep Φ Ψ :
    Fractional Φ → Fractional Ψ → Fractional (λ q, Φ q ∗ Ψ q)%I.
  Proof.
    intros ?? q q'. rewrite !fractional -!assoc. f_equiv.
    rewrite !assoc. f_equiv. by rewrite comm.
  Qed.

  Global Instance fractional_big_sepL {A} l Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (M:=M) (λ q, [∗ list] k↦x ∈ l, Ψ k x q)%I.
  Proof. intros ? q q'. rewrite -big_opL_opL. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepM `{Countable K} {A} (m : gmap K A) Ψ :
    (∀ k (x : A), Fractional (Ψ k x)) →
    Fractional (M:=M) (λ q, [∗ map] k↦x ∈ m, Ψ k x q)%I.
  Proof. intros ? q q'. rewrite -big_opM_opM. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepS `{Countable A} (X : gset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (M:=M) (λ q, [∗ set] x ∈ X, Ψ x q)%I.
  Proof. intros ? q q'. rewrite -big_opS_opS. by setoid_rewrite fractional. Qed.

  Global Instance fractional_big_sepMS `{Countable A} (X : gmultiset A) Ψ :
    (∀ x, Fractional (Ψ x)) →
    Fractional (M:=M) (λ q, [∗ mset] x ∈ X, Ψ x q)%I.
  Proof. intros ? q q'. rewrite -big_opMS_opMS. by setoid_rewrite fractional. Qed.

  (** Mult instances *)

  Global Instance mult_fractional_l Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (q * p)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mult_plus_distr_l. by apply H.
  Qed.
  Global Instance mult_fractional_r Φ Ψ p :
    (∀ q, AsFractional (Φ q) Ψ (p * q)) → Fractional Φ.
  Proof.
    intros H q q'. rewrite ->!as_fractional, Qp_mult_plus_distr_r. by apply H.
  Qed.

  (* REMARK: These two instances do not work in either direction of the
     search:
       - In the forward direction, they make the search not terminate
       - In the backward direction, the higher order unification of Φ
         with the goal does not work. *)
  Instance mult_as_fractional_l P Φ p q :
    AsFractional P Φ (q * p) → AsFractional P (λ q, Φ (q * p)%Qp) q.
  Proof.
    intros H. split. apply H. eapply (mult_fractional_l _ Φ p).
    split. done. apply H.
  Qed.
  Instance mult_as_fractional_r P Φ p q :
    AsFractional P Φ (p * q) → AsFractional P (λ q, Φ (p * q)%Qp) q.
  Proof.
    intros H. split. apply H. eapply (mult_fractional_r _ Φ p).
    split. done. apply H.
  Qed.

  (** Proof mode instances *)
  Global Instance from_and_fractional_fwd P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    FromAnd false P P1 P2.
  Proof. by rewrite /FromAnd=>-[-> ->] [-> _] [-> _]. Qed.
  Global Instance from_sep_fractional_bwd P P1 P2 Φ q1 q2 :
    AsFractional P1 Φ q1 → AsFractional P2 Φ q2 → AsFractional P Φ (q1 + q2) →
    FromAnd false P P1 P2 | 10.
  Proof. by rewrite /FromAnd=>-[-> _] [-> <-] [-> _]. Qed.

  Global Instance from_and_fractional_half_fwd P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    FromAnd false P Q Q | 10.
  Proof. by rewrite /FromAnd -{1}(Qp_div_2 q)=>-[-> ->] [-> _]. Qed.
  Global Instance from_and_fractional_half_bwd P Q Φ q :
    AsFractional P Φ (q/2) → AsFractional Q Φ q →
    FromAnd false Q P P.
  Proof. rewrite /FromAnd=>-[-> <-] [-> _]. by rewrite Qp_div_2. Qed.

  Global Instance into_and_fractional p P P1 P2 Φ q1 q2 :
    AsFractional P Φ (q1 + q2) → AsFractional P1 Φ q1 → AsFractional P2 Φ q2 →
    IntoAnd p P P1 P2.
  Proof.
    (* TODO: We need a better way to handle this boolean here; persistently
       applying mk_into_and_sep (which only works after introducing all
       assumptions) is rather annoying.
       Ideally, it'd not even be possible to make the mistake that
       was originally made here, which is to give this instance for
       "false" only, thus breaking some intro patterns. *)
    intros. apply mk_into_and_sep. rewrite [P]fractional_split //.
  Qed.
  Global Instance into_and_fractional_half p P Q Φ q :
    AsFractional P Φ q → AsFractional Q Φ (q/2) →
    IntoAnd p P Q Q | 100.
  Proof. intros. apply mk_into_and_sep. rewrite [P]fractional_half //. Qed.

  (* The instance [frame_fractional] can be tried at all the nodes of
     the proof search. The proof search then fails almost persistently on
     [AsFractional R Φ r], but the slowdown is still noticeable.  For
     that reason, we factorize the three instances that could have been
     defined for that purpose into one. *)
  Inductive FrameFractionalHyps
      (p : bool) (R : uPred M) (Φ : Qp → uPred M) (RES : uPred M) : Qp → Qp → Prop :=
    | frame_fractional_hyps_l Q q q' r:
       Frame p R (Φ q) Q →
       MakeSep Q (Φ q') RES →
       FrameFractionalHyps p R Φ RES r (q + q')
    | frame_fractional_hyps_r Q q q' r:
       Frame p R (Φ q') Q →
       MakeSep Q (Φ q) RES →
       FrameFractionalHyps p R Φ RES r (q + q')
    | frame_fractional_hyps_half q :
       AsFractional RES Φ (q/2) →
       FrameFractionalHyps p R Φ RES (q/2) q.
  Existing Class FrameFractionalHyps.
  Global Existing Instances frame_fractional_hyps_l frame_fractional_hyps_r
    frame_fractional_hyps_half.

  Global Instance frame_fractional p R r Φ P q RES:
    AsFractional R Φ r → AsFractional P Φ q →
    FrameFractionalHyps p R Φ RES r q →
    Frame p R P RES.
  Proof.
    rewrite /Frame=>-[HR _][->?]H.
    revert H HR=>-[Q q0 q0' r0|Q q0 q0' r0|q0].
    - rewrite fractional=><-<-. by rewrite assoc.
    - rewrite fractional=><-<-=>_.
      by rewrite (comm _ Q (Φ q0)) !assoc (comm _ (Φ _)).
    - move=>-[-> _]->. by rewrite uPred.persistently_if_elim -fractional Qp_div_2.
  Qed.
End fractional.
