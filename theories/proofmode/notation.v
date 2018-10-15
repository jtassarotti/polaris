From iris.proofmode Require Import coq_tactics environments.
From stdpp Require Export strings.
Set Default Proof Using "Type".

Delimit Scope proof_scope with env.
Arguments Envs _ _%proof_scope _%proof_scope.
Arguments Enil {_}.
Arguments Esnoc {_} _%proof_scope _%string _%uPred_scope.

Notation "" := Enil (only printing) : proof_scope.
Notation "Γ H : P" := (Esnoc Γ (INamed H) P)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  P '//'", only printing) : proof_scope.
Notation "Γ '_' : P" := (Esnoc Γ (IAnon _) P)
  (at level 1, P at level 200,
   left associativity, format "Γ '_'  :  P '//'", only printing) : proof_scope.

Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Γ Δ) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Q '//'", only printing) :
  stdpp_scope.
Notation "Δ '--------------------------------------' ∗ Q" :=
  (envs_entails (Envs Enil Δ) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Δ '--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.
Notation "Γ '--------------------------------------' □ Q" :=
  (envs_entails (Envs Γ Enil) Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Q '//'", only printing)  : stdpp_scope.
Notation "'--------------------------------------' ∗ Q" := (envs_entails (Envs Enil Enil) Q%I)
  (at level 1, Q at level 200, format "'--------------------------------------' ∗ '//' Q '//'", only printing) : stdpp_scope.
