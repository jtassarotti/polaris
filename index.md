# Polaris Artifact

This is the website for the artifact accompanying the paper:

A Separation Logic for Concurrent Randomized Programs
Joseph Tassarotti, Robert Harper

The artifact is a Coq development which formalizes the results described in the
paper, by modifying the Iris program logic Coq development. It is available as
either a source tar ball, or a virtual machine image containing all proof
scripts pre-built. Both options contain an HTML outline that gives clickable
links from definitions/theorems in the paper to where they occur in the
development, displayed using HTML generated via coqdoc.

## Compiling from Source

This version is known to compile with the following opam packages:

 - coq                                8.8.2
 - coq-coquelicot                     3.0.2
 - coq-mathcomp-ssreflect             1.7.0
 - coq-stdpp                          1.1.0
 - coq-flocq                          3.0.0
 - coq-interval                       3.4.0
 - coq-bignums                        8.8.0

If you download and unzip the tarball, the directory contains a folder called
README.md (this markdown is also pre-rendered as README.html for convenience)
which describes how to build, access the HTML outline, and discusses axioms
used.

## Virtual Machine

The virtual machine image should boot directly into a user called "aec"
(password is "aec").  On the desktop you will see a folder called
"iris-coq-prob" which contains the built sources. Inside that folder is
README.md (or README.html) which describes how to (re-)build, access the HTML
outline, and discusses axioms used.

The virtual machine has Emacs+ProofGeneral and coqide installed, which can both
be used to inspect the development.

**Note:** The virtual machine is configured to use 6.5gb of memory. You can
   boot and interact with the pre-built sources using far less, but if you
   intend to rebuild the source, be aware that the skiplist example will not
   build if too little memory is used.

## Differences from Original Paper

We have begun to incorporate changes suggested by reviewers of the original
submitted paper (as well as from other feedback we have received). Therefore,
the paper uploaded to HotCRP for the AEC is different from the originally
submitted version. There are two differences that actually affect the artifact.
The Coq code has already been updated for these changes, but we just list them
here to make transparent what has changed:

1. The definition of non-deterministic couplings has been simplified and
generalized. The original paper first described a restricted notion, then
defined a coarser relation called "non-deterministic couplings up to
irrelevance" in the appendix, using a somewhat undermotivated construction. The
new version just defines the coarse relation directly in the paper in a new way
and simply calls this "non-deterministic couplings".

2. We have simplified the concurrent semantics and soundness statements for the
logic slightly. In the original paper, there was an additional assumption on the
soundness statement of the logic which required the scheduler to be
"well-formed" (which said that it only tried to select threads that could take a
step). This assumption was not actually necessary so we have removed it. In
addition. schedulers used to be functions of type Trace -> Option nat instead of
Trace -> nat, meaning that they could return None (which represented not
selecting a thread to step), in which case the program executed a stutter
step. This additional flexibility is not really needed now that we have removed
the "well-formed" assumption from the soundness statement, so we have removed
it.
