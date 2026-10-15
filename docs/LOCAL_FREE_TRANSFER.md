# Local free extensions: common finite C0 / CF lemmas

The core argument for closure-components in both sparse-graph classes is a
finite *relative predimension identity*, not a separate construction
for each class.

## Setup

Work in a finite simple graph G with vertex sets P ⊆ A, B disjoint
from A, and **no graph edge from B to A\P**. Write E=P∪B and C=A∪B.
For every S⊆B,

    δ(A∪S) - δ(A) = δ(P∪S) - δ(P).

More generally, subtract the formulas for S⊆T⊆B to compare the
predimension increment above corresponding intermediate sets
A∪S and P∪S. This identifies *all* intermediate-set inequalities,
not just the predimension of the final structures.

## Exported formal statements

Module: BigHrushovski/LocalFreeTransfer.lean

* GraphOn.localFreeStrong_iff:
  P is strong in E if and only if A is strong in C.
* GraphOn.localFreeDClosed_iff:
  P is strictly d-closed in E if and only if A is strictly
  d-closed in C.
* GraphOn.localFreeTransfer:
  packages both equivalences together with the already audited
  GraphOn.minimalStrongStep_free_iff.

All require the explicit inclusion, disjointness, and no-cross
hypotheses. No generic limit, vertex enumeration, uniform closure
bound, or graph sparsity assumption is hidden in the statements.
The proofs use the earlier GraphOn.local_relative_predim calculation.

The common finite interface can be used in C0 to transport minimal
strong closure-components across a free graph amalgam. For CF it
transports the *strict* d-closedness inequalities for the local
minimal-support construction.

**Now certified:** [Lean PR #125](https://github.com/janhubicka/lean-big-hrushowski/pull/125)
proves the *minimal d-closed* extension equivalence across the
whole interval of intermediate d-closed sets, not only strict
d-closedness of its endpoints. [PR #126](https://github.com/janhubicka/lean-big-hrushowski/pull/126)
certifies the second factor under the additional P≤d A hypothesis.
[PR #128](https://github.com/janhubicka/lean-big-hrushowski/pull/128)
constructs finite d-closed hulls and minimal decompositions, and
[PR #129](https://github.com/janhubicka/lean-big-hrushowski/pull/129)
recovers the canonical old-neighbour support of every minimal step.
None of these constructs a countable functional Fraïssé limit;
see [CF_FINITE_CLOSURE.md](CF_FINITE_CLOSURE.md).

## Four adversarial challenges

**Intermediate sets.** Proving the equality only for S=B is not
enough; strong and d-closed embeddings quantify over every S⊆B.
The formal calculation quantifies over all intermediates, and the
regression enumerates them exhaustively on small graphs.

**No-cross condition.** It cannot be dropped. With P empty,
A={a0,a1,a2}, B={b}, and three old-to-new edges a0b,a1b,a2b,
P is strong in B, whereas A is not strong in A∪B.
The same example defeats strict d-closedness and minimal strongness.

**Second factor.** The equivalences concern P≤E and A≤C.
They do not by themselves establish E≤C; for strict d-closedness,
that additionally follows from P≤d A and the graph free-amalgam
identity for subsets of A\P. The CF manuscript explicitly supplies
this separate hypothesis and calculation.

**Named unary functions.** No-cross and minimality preserve graph
predimensions. Simultaneous transport of the *complete vertex-valued*
unary closures of two independent functional factors needs further
component-index and dependency-path proofs. This remains open for
the general two-sided C0 functional amalgam, irrespective of the
finite regressions.

## Regression and maintenance

scripts/check_cf_strict_local.py enumerates all labelled graphs on
up to five vertices and every partition into P, A\P, B satisfying
no-cross. It now checks weak strongness, strict d-closedness, minimal
strongness, minimal d-closedness and the intermediate d-closed
correspondence, with negative controls for weakened hypotheses.
The checker is a finite diagnostic,
not a general proof.

scripts/check_c0_explicit_amalgam.py remains the stronger functional
two-sided test. The older duplicate check_c0_common_base.py was
removed; all of its finite configurations and original assertions
are subsumed by the retained checker.

The independent-component swap theorem is a valid additional
finite result but is no longer used by the frontloading argument.
Its unused import in C0OrientationInvariantValues has been removed;
the theorem itself is retained as a separate optional library result.
