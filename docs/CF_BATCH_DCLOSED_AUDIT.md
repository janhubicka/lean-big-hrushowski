# Adversarial audit — strict d-closure of the entire tagged C_F batch
15 October 2026

The theorem under examination is a concrete finite result about
the *entire* request-tagged graph, not merely its individual local
pieces. Write U for the literal old-stage vertex set and, for a
finite set D of completed requests, put

    Prefix(D) = U ∪ ⋃_{r∈D} B_r.

The intended theorem asserts U≤d Prefix(D) for every D, including
the full finite request catalogue. Each strict inequality applies
to *every* intermediate subset, even when it meets several blocks.

## Four adversarial mathematical referees

**1. Actual-support referee.** A named support P_r is strictly
d-closed inside the induced old graph U by the StageRequest record.
At a later prefix, this alone is insufficient: we must first
know U≤d Prefix(D). Strict transitivity then yields
P_r≤d Prefix(D). The induction proves precisely this invariant,
rather than assuming P_r stays closed as blocks are added.

**2. Boundary and freshness referee.** If r is not yet attached,
B_r is disjoint from the current prefix because request tags are
distinct and no fresh vertex equals an old vertex. Every edge
from B_r to Prefix(D) must end in P_r. An edge to an old vertex
outside P_r contradicts the verified actual support-boundary
theorem, while an edge to any completed block contradicts
the verified no-cross-fresh theorem. These facts are proved
for the *constructed graph*, not postulated as new assumptions.

**3. Relative-to-global referee.** The normalized local type
is minimal strict d-closed with exact support in its finite
induced image. The complete image and support identities make
these hypotheses available to the one-block persistence theorem
at each prefix. That theorem gives Prefix(D)≤d
Prefix(D)∪B_r. Induction and strict transitivity conclude
U≤d Prefix(D∪{r}). In particular the final result is stronger
than pairwise block separation: it covers intermediate sets
meeting arbitrarily many different new blocks.

**4. Class and countable-limit referee.** The current statement is
about arbitrary finite graph predimensions and a literal complete
tagged request catalogue. It does not show that the resulting
finite graph satisfies the growth-function inequalities defining
the restricted class C_F. This additional class-preservation
step must use the published d-closed free-amalgamation theorem
for C_F, and only then may the finite levels be iterated.
The countable generic, block-root recovery and embedding monoid
remain unverified by the finite tagged graph theorem.

## Independent finite regression

The existing actual-tagged-graph checker has been strengthened
to process each request chronologically. For every nonempty
subset of the next fresh block, it verifies the exact
relative-predimension identity over the current prefix and
strict positivity. In the final batch, it also samples finite
intermediate sets meeting one, two and several fresh blocks,
including non-singleton minimal increments.

These bounded diagnostics complement the general Lean proof;
they cannot replace the quantification over all finite subsets.
The exact finite theorem is GREEN only if its final integrated
Lean build, standard-axiom audit and placeholder scan succeed.
