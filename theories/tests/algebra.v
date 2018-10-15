From iris.base_logic.lib Require Import invariants.

Section tests.
  Context `{invG Σ}.

  Program Definition test : (iProp Σ -n> iProp Σ) -n> (iProp Σ -n> iProp Σ) :=
    λne P v, (▷ (P v))%I.
  Solve Obligations with solve_proper.

End tests.
