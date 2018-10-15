Tactic overview
===============

Many of the tactics below apply to more goals than described in this document
since the behavior of these tactics can be tuned via instances of the type
classes in the file [proofmode/classes](proofmode/classes.v). Most notable, many
of the tactics can be applied when the to be introduced or to be eliminated
connective appears under a later, an update modality, or in the conclusion of a
weakest precondition.

Applying hypotheses and lemmas
------------------------------

- `iExact "H"`  : finish the goal if the conclusion matches the hypothesis `H`
- `iAssumption` : finish the goal if the conclusion matches any hypothesis
- `iApply pm_trm` : match the conclusion of the current goal against the
  conclusion of `pm_trm` and generates goals for the premises of `pm_trm`. See
  proof mode terms below.
  If the applied term has more premises than given specialization patterns, the
  pattern is extended with `[] ... []`.  As a consequence, all unused spatial
  hypotheses move to the last premise.

Context management
------------------

- `iIntros (x1 ... xn) "ipat1 ... ipatn"` : introduce universal quantifiers
  using Coq introduction patterns `x1 ... xn` and implications/wands using proof
  mode introduction patterns `ipat1 ... ipatn`.
- `iClear (x1 ... xn) "selpat"` : clear the hypotheses given by the selection
  pattern `selpat` and the Coq level hypotheses/variables `x1 ... xn`.
- `iRevert (x1 ... xn) "selpat"` : revert the hypotheses given by the selection
  pattern `selpat` into wands, and the Coq level hypotheses/variables
  `x1 ... xn` into universal quantifiers. Persistent hypotheses are wrapped into
  the persistence modality.
- `iRename "H1" into "H2"` : rename the hypothesis `H1` into `H2`.
- `iSpecialize pm_trm` : instantiate universal quantifiers and eliminate
  implications/wands of a hypothesis `pm_trm`. See proof mode terms below.
- `iSpecialize pm_trm as #` : instantiate universal quantifiers and eliminate
  implications/wands of a hypothesis whose conclusion is persistent. In this
  case, all hypotheses can be used for proving the premises, as well as for
  the resulting goal.
- `iPoseProof pm_trm as (x1 ... xn) "ipat"` : put `pm_trm` into the context and
  eliminates it. This tactic is essentially the same as `iDestruct` with the
  difference that when `pm_trm` is a non-univerisally quantified spatial
  hypothesis, it will not throw the hypothesis away.
- `iAssert P with "spat" as "ipat"` : generates a new subgoal `P` and adds the
  hypothesis `P` to the current goal. The specialization pattern `spat`
  specifies which hypotheses will be consumed by proving `P`. The introduction
  pattern `ipat` specifies how to eliminate `P`.
  In case all branches of `ipat` start with a `#` (which causes `P` to be moved
  to the persistent context) or with an `%` (which causes `P` to be moved to the
  pure Coq context), then one can use all hypotheses for proving `P` as well as
  for proving the current goal.
- `iAssert P as %cpat` : assert `P` and eliminate it using the Coq introduction
  pattern `cpat`. All hypotheses can be used for proving `P` as well as for
  proving the current goal.

Introduction of logical connectives
-----------------------------------

- `iPureIntro` : turn a pure goal into a Coq goal. This tactic works for goals
  of the shape `⌜φ⌝`, `a ≡ b` on discrete COFEs, and `✓ a` on discrete CMRAs.

- `iLeft` : left introduction of disjunction.
- `iRight` : right introduction of disjunction.

- `iSplit` : introduction of a conjunction, or separating conjunction provided
  one of the operands is persistent.
- `iSplitL "H1 ... Hn"` : introduction of a separating conjunction. The
  hypotheses `H1 ... Hn` are used for the left conjunct, and the remaining ones
  for the right conjunct. Persistent hypotheses are ignored, since these do not
  need to be split.
- `iSplitR "H0 ... Hn"` : symmetric version of the above.
- `iExist t1, .., tn` : introduction of an existential quantifier.

Elimination of logical connectives
----------------------------------

- `iExFalso` : Ex falso sequitur quod libet.
- `iDestruct pm_trm as (x1 ... xn) "ipat"` : elimination of a series of
  existential quantifiers using Coq introduction patterns `x1 ... xn`, and
  elimination of an object level connective using the proof mode introduction
  pattern `ipat`.
  In case all branches of `ipat` start with a `#` (which causes the hypothesis
  to be moved to the persistent context) or with an `%` (which causes the
  hypothesis to be moved to the pure Coq context), then one can use all
  hypotheses for proving the premises of `pm_trm`, as well as for proving the
  resulting goal. Note that in this case the hypotheses still need to be
  subdivided among the spatial premises.
- `iDestruct pm_trm as %cpat` : elimination of a pure hypothesis using the Coq
  introduction pattern `cpat`. When using this tactic, all hypotheses can be
  used for proving the premises of `pm_trm`, as well as for proving the
  resulting goal.

Separating logic specific tactics
---------------------------------

- `iFrame (t1 .. tn) "selpat"` : cancel the Coq terms (or Coq hypotheses)
  `t1 ... tn` and Iris hypotheses given by `selpat` in the goal. The constructs
  of the selection pattern have the following meaning:

  + `%` : repeatedly frame hypotheses from the Coq context.
  + `#` : repeatedly frame hypotheses from the persistent context.
  + `∗` : frame as much of the spatial context as possible.

  Notice that framing spatial hypotheses makes them disappear, but framing Coq
  or persistent hypotheses does not make them disappear.

  This tactic finishes the goal in case everything in the conclusion has been
  framed.
- `iCombine "H1" "H2" as "H"` : turns `H1 : P1` and `H2 : P2` into
  `H : P1 ∗ P2`.

Modalities
----------

- `iModIntro` : introduction of a modality that is an instance of the
  `FromModal` type class. Instances include: later, except 0, basic update and
  fancy update.
- `iMod pm_trm as (x1 ... xn) "ipat"` : eliminate a modality `pm_trm` that is
  an instance of the `ElimModal` type class. Instances include: later, except 0,
  basic update and fancy update.

The persistence and plainness modalities
----------------------------------------

- `iAlways` : introduce a persistence or plainness modality and the spatial
  context. In case of a plainness modality, the tactic will prune all persistent
  hypotheses that are not plain.

The later modality
------------------

- `iNext n` : introduce `n` laters by stripping that number of laters from all
  hypotheses. If the argument `n` is not given, it strips one later if the
  leftmost conjunct is of the shape `▷ P`, or `n` laters if the leftmost
  conjunct is of the shape `▷^n P`.
- `iLöb as "IH" forall (x1 ... xn) "selpat"` : perform Löb induction by
  generating a hypothesis `IH : ▷ goal`. The tactic generalizes over the Coq
  level variables `x1 ... xn`, the hypotheses given by the selection pattern
  `selpat`, and the spatial context.

Induction
---------

- `iInduction x as cpat "IH" forall (x1 ... xn) "selpat"` : perform induction on
  the Coq term `x`. The Coq introduction pattern is used to name the introduced
  variables. The induction hypotheses are inserted into the persistent context
  and given fresh names prefixed `IH`. The tactic generalizes over the Coq level
  variables `x1 ... xn`, the hypotheses given by the selection pattern `selpat`,
  and the spatial context.

Rewriting
---------

- `iRewrite pm_trm` : rewrite an equality in the conclusion.
- `iRewrite pm_trm in "H"` : rewrite an equality in the hypothesis `H`.

Iris
----

- `iInv N as (x1 ... xn) "ipat" "Hclose"` : open the invariant `N`, the update
  for closing the invariant is put in a hypothesis named `Hclose`.

Miscellaneous
-------------

- The tactic `done` is extended so that it also performs `iAssumption` and
  introduces pure connectives.
- The proof mode adds hints to the core `eauto` database so that `eauto`
  automatically introduces: conjunctions and disjunctions, universal and
  existential quantifiers, implications and wand, plainness, persistence, later
  and update modalities, and pure connectives.

Selection patterns
==================

Selection patterns are used to select hypotheses in the tactics `iRevert`,
`iClear`, `iFrame`, `iLöb` and `iInduction`. The proof mode supports the
following _selection patterns_:

- `H` : select the hypothesis named `H`.
- `%` : select the entire pure/Coq context.
- `#` : select the entire persistent context.
- `∗` : select the entire spatial context.

Introduction patterns
=====================

Introduction patterns are used to perform introductions and eliminations of
multiple connectives on the fly. The proof mode supports the following
_introduction patterns_:

- `H` : create a hypothesis named `H`.
- `?` : create an anonymous hypothesis.
- `_` : remove the hypothesis.
- `$` : frame the hypothesis in the goal.
- `[ipat1 ipat2]` : (separating) conjunction elimination. In order to eliminate
  conjunctions `P ∧ Q` in the spatial context, one of the following conditions
  should hold:
  + Either the proposition `P` or `Q` should be persistent.
  + Either `ipat1` or `ipat2` should be `_`, which results in one of the
    conjuncts to be thrown away.
- `[ipat1|ipat2]` : disjunction elimination.
- `[]` : false elimination.
- `%` : move the hypothesis to the pure Coq context (anonymously).
- `->` and `<-` : rewrite using a pure Coq equality
- `# ipat` : move the hypothesis to the persistent context.
- `> ipat` : eliminate a modality (if the goal permits).

Apart from this, there are the following introduction patterns that can only
appear at the top level:

- `{selpat}` : clear the hypotheses given by the selection pattern `selpat`.
  Items of the selection pattern can be prefixed with `$`, which cause them to
  be framed instead of cleared.
- `!%` : introduce a pure goal (and leave the proof mode).
- `!#` : introduce an persistence or plainness modality (by calling `iAlways`).
- `!>` : introduce a modality (by calling `iModIntro`).
- `/=` : perform `simpl`.
- `//` : perform `try done` on all goals.
- `//=` : syntactic sugar for `/= //`
- `*` : introduce all universal quantifiers.
- `**` : introduce all universal quantifiers, as well as all arrows and wands.

For example, given:

        ∀ x, x = 0 ⊢ □ (P → False ∨ □ (Q ∧ ▷ R) -∗ P ∗ ▷ (R ∗ Q ∧ x = pred 2)).

You can write

        iIntros (x) "% !# $ [[] | #[HQ HR]] /= !>".

which results in:

        x : nat
        H : x = 0
        ______________________________________(1/1)
        "HQ" : Q
        "HR" : R
        --------------------------------------□
        R ∗ Q ∧ x = 1


Specialization patterns
=======================

Since we are reasoning in a spatial logic, when eliminating a lemma or
hypothesis of type ``P_0 -∗ ... -∗ P_n -∗ R``, one has to specify how the
hypotheses are split between the premises. The proof mode supports the following
_specification patterns_ to express splitting of hypotheses:

- `H` : use the hypothesis `H` (it should match the premise exactly). If `H` is
  spatial, it will be consumed.

- `[H1 .. Hn]` and `[H1 .. Hn //]` : generate a goal for the premise with the
  (spatial) hypotheses `H1 ... Hn` and all persistent hypotheses. The spatial
  hypotheses among `H1 ... Hn` will be consumed, and will not be available for
  subsequent goals. Hypotheses prefixed with a `$` will be framed in the
  goal for the premise. The pattern can be terminated with a `//`, which causes
  `done` to be called to close the goal (after framing).
- `[-H1 ... Hn]` and `[-H1 ... Hn //]` : the negated forms of the above
  patterns, where the goal for the premise will have all spatial premises except
  `H1 .. Hn`.

- `[> H1 ... Hn]` and `[> H1 ... Hn //]` : like the above patterns, but these
  patterns can only be used if the goal is a modality `M`, in which case
  the goal for the premise will be wrapped in the modality `M`.
- `[> -H1 ... Hn]` and `[> -H1 ... Hn //]` : the negated forms of the above
  patterns.

- `[# $H1 .. $Hn]` and `[# $H1 .. $Hn //]` : generate a goal for a persistent
  premise in which all hypotheses are available. This pattern does not consume
  any hypotheses; all hypotheses are available in the goal for the premise, as
  well in the subsequent goal. The hypotheses `$H1 ... $Hn` will be framed in
  the goal for the premise. These patterns can be terminated with a `//`, which
  causes `done` to be called to close the goal (after framing).
- `[%]` and `[% //]` : generate a Coq goal for a pure premise. This pattern
  does not consume any hypotheses. The pattern can be terminated with a `//`,
  which causes `done` to be called to close the goal.

- `[$]` : solve the premise by framing. It will first repeatedly frame the
  spatial hypotheses, and then repeatedly frame the persistent hypotheses.
  Spatial hypothesis that are not framed are carried over to the subsequent
  goal.
- `[> $]` : like the above pattern, but this pattern can only be used if the
  goal is a modality `M`, in which case the goal for the premise will be wrapped
  in the modality `M` before framing.
- `[# $]` : solve the persistent premise by framing. It will first repeatedly
  frame the spatial hypotheses, and then repeatedly frame the persistent
  hypotheses. This pattern does not consume any hypotheses.

For example, given:

        H : □ P -∗ P 2 -∗ R -∗ x = 0 -∗ Q1 ∗ Q2

One can write:

        iDestruct ("H" with "[#] [H1 $H2] [$] [% //]") as "[H4 H5]".


Proof mode terms
================

Many of the proof mode tactics (such as `iDestruct`, `iApply`, `iRewrite`) can
take both hypotheses and lemmas, and allow one to instantiate universal
quantifiers and implications/wands of these hypotheses/lemmas on the fly.

The syntax for the arguments of these tactics, called _proof mode terms_, is:

        (H $! t1 ... tn with "spat1 .. spatn")

Here, `H` can be both a hypothesis, as well as a Coq lemma whose conclusion is
of the shape `P ⊢ Q`. In the above, `t1 ... tn` are arbitrary Coq terms used
for instantiation of universal quantifiers, and `spat1 .. spatn` are
specialization patterns to eliminate implications and wands.

Proof mode terms can be written down using the following short hands too:

        (H with "spat1 .. spatn")
        (H $! t1 ... tn)
        H

