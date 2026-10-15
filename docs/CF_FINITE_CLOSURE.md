# Finite d-closed support library for C_F

Certified checkpoint: [PR #129](https://github.com/janhubicka/lean-big-hrushowski/pull/129),
[GitHub Actions run 38668876684](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38668876684):
**509 declarations** audited using only standard logical axioms,
**117 Lean files** scanned with no proof placeholders, and all 55
workflow steps successful.

## Definitions

* Predimension.IsDClosed a b: a⊆b and δ(a)<δ(x) for every
  intermediate a⊊x⊆b. This is stricter than self-sufficiency.
* Predimension.IsMinimalDClosedStep a b: a is d-closed in b,
  a≠b, and no intermediate d-closed z satisfies a⊊z⊊b.
* Predimension.dClosedHull s c: least d-closed subset of the
  finite ambient c containing s (for s⊆c). This hull is built
  from intersections of d-closed vertex sets, not from an
  external countable closure operator.
* GraphOn.oldNeighbourSet A B: vertices of A with a graph
  neighbour in the new block B.

## Public results and reuse

| Theorem | Exact result |
| --- | --- |
| GraphOn.localFreeDClosed_iff | Strict d-closedness transfers both ways under no-cross, without assuming P≤d A |
| GraphOn.dClosed_intermediate_free_iff | Every corresponding intermediate strict d-closedness condition transfers |
| GraphOn.minimalDClosedStep_free_iff | Minimal d-closed steps transfer and reflect |
| GraphOn.dClosed_local_right_factor | The *second* factor P∪B is d-closed in A∪B when P≤d A |
| Predimension.finite_minimal_decomposition_of_dClosed_absolute | Every finite a≤d b factors into finitely many nonempty minimal d-closed steps |
| Predimension.dClosedHull_dclosed; dClosedHull_least | A finite generated hull is d-closed and contained in every closed superset |
| Predimension.minimalDClosedStep_iff_every_generator | In a nontrivial a≤d b, minimality means cl_b^d(ax)=b for every x∈b\a |
| GraphOn.canonical_dClosed_local_support | For A<_d A∪B, the least support P=cl_A^d(N) gives P≤d A, no crossing edges, P<_d P∪B, P∪B≤d A∪B and cl_P^d(N)=P |

The common numerical observation for P⊆A, A∩B=∅ and no
edges between B and A\P is

    δ(A∪S)−δ(A) = δ(P∪S)−δ(P)    for every S⊆B.

It identifies the whole interval of intermediate predimension
inequalities. For the **second factor**, one needs the genuinely
additional hypothesis P≤d A.

The K4 example tests the distinction between strong and d-closed
minimality: the empty set has a minimal d-closed extension to K4,
although a singleton is strong in K4. A bounded regression checks
the canonical support theorem on 33,867 old/new partitions, including
3,847 minimal d-closed extensions, with no mismatches.

## Formal boundary

These results are for arbitrary finite simple graph predimensions.
They do **not** establish that a particular growth-function subclass
C_F is closed under the permitted free amalgams. They do not
construct its countable Fraïssé limit.

The next independent obligations are:
1. incorporate the assumed C_F closure bound into a finite
   catalogue of ordered local extension types over a fixed base;
2. define the successive finite levels and prove that the
   schedule realizes every d-closed extension requirement;
3. formalize the finite block-root functions and prove the
   embedding-lift/monoid claims.

The abstract Milliken and Ellentuck libraries become relevant
only when these concrete approximation and embedding data
have been constructed.

For the exact theorem correspondence see VALIDATION.md.
