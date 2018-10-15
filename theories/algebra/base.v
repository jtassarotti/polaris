From mathcomp Require Export ssreflect.
From stdpp Require Export prelude.
Set Default Proof Using "Type".
(* Reset options set by the ssreflect plugin to their defaults *)
Global Set Bullet Behavior "Strict Subproofs".
Global Open Scope general_if_scope.
Global Unset Asymmetric Patterns.
Ltac done := stdpp.tactics.done.
