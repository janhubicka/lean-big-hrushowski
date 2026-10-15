# Adversarial audit — recursive finite C_F tagged tower

16 October 2026

## Certified claims intended by this change

The earlier modules construct one finite graph U' from a finite graph U,
using the complete finite set of admissible named-support requests.
The new FiniteStage packages the finite carrier, its graph, and its
finite decidable equality. The primitive recursive sequence starts
with Fin 0 and at each successor stage applies **the actual**
CFStageCatalogue.levelGraph with Allowed = GrowthAllowedLocal F and
bound(P) = K(|P|).

The mathematical conclusions are:

* Every stage has a finite carrier, with no untyped identifications
  between blocks or with old vertices.
* The old inclusion is literally Sum.inl. It preserves and
  **reflects** the entire adjacency relation, not just edges.
* The old stage is strictly d-closed in the full next level,
  including intermediate subsets meeting several new blocks.
* If old stages belong to the exact growth-function class and the
  restricted d-closed free-amalgamation condition holds at every
  stage, then so do the new stages.

## Four adversarial referee passes

1. **Carrier/identity referee.** The domain at step n+1 is
   U_n plus fresh pairs (request tag, local ordinal). We never
   silently identify two isomorphic requests. The tower uses
   genuine dependent finite types; there is no unproved choice
   of a common natural-number numbering.

2. **Inducedness referee.** The old graph inside the new level
   is induced: levelGraph_old_iff rules out new edges *and*
   preserves existing ones on old-old pairs. If the recursive
   transition proved only a homomorphism, any later claim about
   d-closure or complete local codes could fail.

3. **Predimension referee.** Strict d-closedness of the old
   part is the previously verified arbitrary-batch theorem.
   Ordinary weak strongness is insufficient for the manuscript's
   prescribed `<=d` embeddings. The stage-step statement is
   finite and is not yet global closure in a countable union.

4. **Growth and completeness referee.** The type of admissible
   requests uses the *real* growth class F, not a convenient
   2-sparse superset. Class membership of the next stage depends
   on the explicit restricted d-closed free-join hypothesis.
   An arbitrary numeric bound K might omit necessary minimal
   extensions: choosing K=0 can make all catalogues empty and
   the tower can become stationary. The published uniform closure
   bound must be used to choose and justify K before asserting
   genericity or infinitude.

## Precise scope of the new API

This module does not yet build the countable direct-limit graph,
does not show that every finite set of the limit lies in a stage,
does not supply the singleton request, and does not identify
the limit with M_F. Those tasks require constructing a canonical
countable carrier from the successive literal Sum.inl embeddings,
transporting the finite exact response theorem through it, and
applying the existing finite minimal-response induction.

Further functional obligations: finite block ancestry, all
function values and their domains, and H(R(v))=C(v).

The four mathematical audits are separated hostile proof passes
made internally. They are not independent external human referees.
A green manuscript validation marker is permitted only after the
exact Lean declaration compiles and its standard-axiom and
placeholder checks pass at the final committed head.
