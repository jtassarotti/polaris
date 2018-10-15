# POLARIS COQ DEVELOPMENT

This is the Coq development of Polaris, an extension of the [Iris
Project](http://iris-project.org)  to support probabilistic relational
reasoning. The following README is adapted in part from that of the original
Iris development.

## Prerequisites

This version is known to compile with the following opam packages:

 - coq                                8.8.2
 - coq-coquelicot                     3.0.2
 - coq-mathcomp-ssreflect             1.7.0
 - coq-stdpp                          1.1.0
 - coq-flocq                          3.0.0
 - coq-interval                       3.4.0
 - coq-bignums                        8.8.0

When building from source, we recommend to use opam (1.2.2 or newer) for
installing Iris's dependencies.  This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

You then should be able to run `make build-dep` to get these dependencies installed.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores. (WARNING: the examples can take a long time to build). If you do so,
one of the files will print axioms used for a small example proof (see below for the list
of axioms used in the development).

## Clickable HTML Correspondence Table

The file [outline.html](outline.html) provides a table giving a correspondence between
definitions/theorems in the (revised) paper and their location in the Coq
development, as suggested in the [Proof Artifact Guidelines](https://docs.google.com/document/d/18IOZR_-zFUDB-2KT-VSDTcl3suge_bSX2758W1kHm5o/edit#heading=h.632p0wk53q0m)
by Marianna Rapoport. Clickable links are given to spots in the HTML version of the
development produced using coqdoc. These should be prebuilt in versions of
this package built for artifact review, but if they do not exist, you can
create them by running `make html` after building the development.

## Axioms

The following list of axioms is produced when executing the `Print Assumptions` command
in [theories/tests/prob_heap_lang.v](theories/tests/prob_heap_lang.v):

```
Axioms:
up : R → Z
total_order_T : ∀ r1 r2 : R, {r1 < r2} + {r1 = r2} + {r1 > r2}
ClassicalEpsilon.constructive_indefinite_description : 
∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
completeness : ∀ E : R → Prop,
               bound E → (∃ x : R, E x) → {m : R | is_lub E m}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
archimed : ∀ r : R, IZR (up r) > r ∧ IZR (up r) - r <= 1
Rplus_opp_r : ∀ r : R, r + - r = 0
Rplus_lt_compat_l : ∀ r r1 r2 : R, r1 < r2 → r + r1 < r + r2
Rplus_comm : ∀ r1 r2 : R, r1 + r2 = r2 + r1
Rplus_assoc : ∀ r1 r2 r3 : R, r1 + r2 + r3 = r1 + (r2 + r3)
Rplus_0_l : ∀ r : R, 0 + r = r
Rplus : R → R → R
Ropp : R → R
Rmult_plus_distr_l : ∀ r1 r2 r3 : R, r1 * (r2 + r3) = r1 * r2 + r1 * r3
Rmult_lt_compat_l : ∀ r r1 r2 : R, 0 < r → r1 < r2 → r * r1 < r * r2
Rmult_comm : ∀ r1 r2 : R, r1 * r2 = r2 * r1
Rmult_assoc : ∀ r1 r2 r3 : R, r1 * r2 * r3 = r1 * (r2 * r3)
Rmult_1_l : ∀ r : R, 1 * r = r
Rmult : R → R → R
Rlt_trans : ∀ r1 r2 r3 : R, r1 < r2 → r2 < r3 → r1 < r3
Rlt_asym : ∀ r1 r2 : R, r1 < r2 → ¬ r2 < r1
Rlt : R → R → Prop
Rinv_l : ∀ r : R, r ≠ 0 → / r * r = 1
Rinv : R → R
R1_neq_R0 : 1 ≠ 0
R1 : R
R0 : R
R : Set
```

With two exceptions, these axioms are all from the Coq standard library's axiomatization of
the real numbers. The two exceptions are:

```
ClassicalEpsilon.constructive_indefinite_description : 
∀ (A : Type) (P : A → Prop), (∃ x : A, P x) → {x : A | P x}
Classical_Prop.classic : ∀ P : Prop, P ∨ ¬ P
```

which are again from Coq's standard library, and are used for classical reasoning.

WARNING: If you try to compile this with Coq 8.8.1, it will list additional
things as "assumptions" that are not assumptions at all. This is caused by a
[bug](https://github.com/coq/coq/issues/8416) in Coq.

## Directory Structure

The development is divided into two main parts. The folder theories/ contains
the the program logic formalization, while proba/theories/ contains a library
for probability theory, and our formalization of the theory
of indexed valuations.

### Original Iris Files and Outline
* The folder [algebra](theories/algebra) contains the COFE and CMRA
  constructions as well as the solver for recursive domain equations.
* The folder [base_logic](theories/base_logic) defines the Iris base logic and
  the primitive connectives.  It also contains derived constructions that are
  entirely independent of the choice of resources.
  * The subfolder [lib](theories/base_logic/lib) contains some generally useful
    derived constructions.  Most importantly, it defines composeable
    dynamic resources and ownership of them; the other constructions depend
    on this setup.
* The folder [program_logic](theories/program_logic) specializes the base logic
  to build Iris, the program logic.   This includes weakest preconditions that
  are defined for any language satisfying some generic axioms, and some derived
  constructions that work for any such language.
* The folder [proofmode](theories/proofmode) contains the Iris proof mode, which
  extends Coq with contexts for persistent and spatial Iris assertions. It also
  contains tactics for interactive proofs in Iris. Documentation can be found in
  [ProofMode.md](ProofMode.md).
* The folder [heap_lang](theories/heap_lang) defines the ML-like concurrent heap
  language, extended with a primitive operation for sampling from Bernoulli distribution.
  * The subfolder [lib](theories/heap_lang/lib) contains a few derived
    constructions within this language, e.g., parallel composition.

### Overview of Probabilistic Extensions
* [program_logic/prob_language.v](theories/program_logic/prob_language.v)
  defines the generic structure of concurrent languages that we consider.
* [program_logic/prob_lifting.v](theories/program_logic/prob_lifting.v)
  gives the generic proof rules for the new probabilistic extensions of weakest precondition.
* [heap_lang/adequacy.v](theories/heap_lang/adequacy.v)
  instantiation of the generic soundness theorem for the particular language we consider in
  the paper. N.B.: in the paper, we state this theorem as if the indexed valuation
  interpretation of the concrete program *always* returned a non-empty list and always
  returned a value; to avoid having to make this term dependently typed to ensure this, here we simply
  return dummy values for the expectation function if the program is not terminated or if the list
  of threads is empty.
* [program_logic/prob_adequacy.v](theories/program_logic/prob_adequacy.v)
  gives the soundness theorem for the probabilistic extensions (that is, the existence of
  an appropriate triple implies the existence of a coupling up to irrelevance), stated
  for a generic language.
* [tests/approx_counter/faa_approx_counter.v](theories/tests/approx_counter/faa_approx_counter.v) develops the
  approximate counter example from the paper, along with the "countTrue" client
  and an additional client not discussed in the
  paper. faa_approx_counter_nomax.v and faa_approx_counter_arb.v contain the
  variations mentioned in section 4.3
* [tests/skiplist/](theories/tests/skiplist) contains the skip list example and client.
    * [code.v](theories/tests/skiplist/code.v) gives the implementation of skip
      lists.
    * [idxval.v](theories/tests/skiplist/idxval.v) is the monadic model.
    * [spec_bundled.v](theories/tests/skiplist/spec_bundled.v) contains the
      Hoare triples for the skip list.
    * [idxval_expected.v](theories/tests/skiplist/idxval_expected.v) derives the
      upper bound on the expected values
    * [client.v](theories/tests/skiplist/client.v) contains a simple example client
      that uses these triples. 

### Library for Probability

* The folder [basic](proba/theories/basic) defines some lemmas missing from ssreflect
  that we found useful.
* The folder [prob](proba/theories/prob) contains a development of discrete probability theory
* The folder [measure](proba/theories/measure) contains a development of basic measure theory and Lebesgue integration(not used here).
* The folder [monad](proba/theories/monad) definition of probability distribution list monad
* The folder [idxval](proba/theories/idxval) contains results on the indexed valuation monad.
    * [irrel_equiv.v](proba/theories/idxval/irrel_equiv.v) gives the notion of non-deterministic couplings and its theory.
    * [extrema.v](proba/theories/idxval/extrema.v) defines expected values and extrema for indexed valuations and sets of them.

At some point this library will probably be split off and distributed as a
separate project (parts of it have been already).