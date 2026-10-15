# Adversarial referee audit: minimal-response induction

16 October 2026

## Statement

Given a finite strict d-closed inclusion A <=d B,
and an arbitrary property Valid(S,f) of a partial realization
encoded by a *total* vertex map f (only its values on S matter
when Valid is instantiated as an embedding property),
assume every minimal d-closed step S < T can extend any Valid(S,f)
to some Valid(T,g) with g literally equal to f on S.
Then any Valid(A,f) extends to Valid(B,g) with g=f on A.

This follows from the certified finite minimal-step decomposition
and is independent of any countable schedule.

## Four hostile checks

1. **Source-fixing referee.** The induction must retain equality of
   maps on every vertex of the original A, not merely the images
   as abstract subgraphs. Equality is composed along each minimal
   step using A subset S. Without this, no labelled extension
   property would follow.

2. **Strictness referee.** The chain's steps are minimal *strictly
   d-closed* extensions, not merely minimal weakly strong steps.
   The decomposition theorem and the step hypothesis must use
   exactly the same notion; silently switching to strongness
   would invalidate the application.

3. **Finite termination referee.** Each proper minimal step adds
   at least one new source vertex. The decomposition from
   CFDClosedDecomposition is finite, so the induction terminates
   without a fairness or countability assumption. The proof
   does not postulate that a countable graph can fulfill the
   local hypotheses.

4. **Instantiation referee.** The abstract Valid predicate can
   record an induced partial graph embedding with a d-closed
   image in a suitable stage. It can also record extra order or
   function-value constraints. However this theorem proves
   none of those properties from scratch: all must be
   preserved by the construction-specific hLocal hypothesis.
   In particular one still needs a coherent countable C_F
   carrier and actual minimal-code completeness.

## Consequence for the manuscript

The finite genericity argument needs only:
  (i) finite minimal d-closed decomposition;
  (ii) one-level response to each minimal step over the *actual*
  old support; and
  (iii) persistence of d-closedness in later finite stages.

There is no necessity to enumerate all arbitrary finite d-closed
extension diagrams with a separate global fair schedule when
each stage attaches all minimal local requests.

This is a reusable proof-composition lemma. Green validation
requires final Lean CI, standard-axiom audit and placeholder scan.

All roles are internal adversarial mathematical checks and do
not constitute external independent referee certification.
