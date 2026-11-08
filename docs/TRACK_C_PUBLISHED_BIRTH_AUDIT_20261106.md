# Track C — published-domain genericity on actual birth vertices

Dependent on literal singleton PR #315 and its all-level coverage
PR #335. The earlier birth-graph uniqueness theorem and published
growth adapter are already verified on main.

## Exact mathematical claim

For F defined on nonnegative reals with nonnegative values:
- F(0)=0, F monotone and unbounded;
- the finite C_F class is closed under strict d-closed free amalgamation;
- every finite C_F member has empty strictly d-closed base;
- the one-vertex member belongs to C_F, represented exactly by F(1)≤2.

The canonical tagged birth graph is induced-isomorphic to any
countable graph on ℕ having the full C_F growth inequality, finite
globally strictly d-closed covers, complete prescribed-base strict
d-closed extension responses, and globally d-closed empty base.

The equality `publishedCardinalGrowth_eq` replaces the real
growth cardinal function by the original published function
without changing any finite membership test. Neither an arbitrary
extension of F to negative values nor an external cutoff is assumed.

## Internal adversarial panel

- **Domain referee:** the only negative-input values of F occur
  through the already verified constant extension, which
  agrees with F at all finite vertex cardinalities.
- **Finite-class referee:** the class free-join and strict
  empty-base hypotheses remain independent of analytic F.
- **Singleton referee:** the numerical F(1)≤2 is precisely
  singleton membership under δ({v})=2, not a consequence of F(0)=0.
- **Countable referee:** comparison graph N must satisfy each of
  four strict finite recognition conditions. A random countable
  graph or merely 2-sparse generic is not sufficient.
- **Map referee:** conclusion concerns a genuine induced
  equivalence of the original birth carrier, preserving and
  reflecting all adjacency and nonadjacency.
- **Certification referee:** this specialization itself must
  compile with an exact axiom audit. The printed strong limit
  M_F has not been explicitly constructed as an object of the
  Lean development; the final paper identification still
  requires connecting its Fraisse characterization to N.

Status: proposed dependent proof, CI pending. These are internal
role-separated checks, not external human referees.
