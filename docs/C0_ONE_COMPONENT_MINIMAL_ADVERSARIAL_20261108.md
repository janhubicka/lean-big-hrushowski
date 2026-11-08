# Track A: adversarial audit of closed one-component intervals

Date: 8 November 2026. Proof: `BigHrushovski/C0OneRemainingComponent.lean`.
The referee roles below are independent **internal mathematical checks**,
not reports by additional human referees.

## Stronger exact theorem

Let `G` have a finite canonical component-index presentation
`κ : V → Fin n` in which every nonempty index step is minimal
strong (empty slots are allowed). For finite sets `S ⊆ Z ⊆ V`,
both closed under the **complete** canonical unary operation, suppose

`Z \ S = component κ (κ x).val`

for one vertex x. Then `G.toPredimension.IsMinimalStrongStep S Z`.
The original `closed_complement_one_component_minimal` theorem
is retained as the corollary `Z=Finset.univ`.

## Referee A: two frontloadings really isolate the interval

Write `a=frontloadIndex κ Z` and
`b=frontloadIndex a S`. The first operation puts every vertex of
Z before every vertex outside it, without changing complete unary
values. Since S⊆Z, the second puts S first. Both reordered
presentations retain all nonempty minimal strong steps by the
previously certified `frontloadIndex_minimal_steps`.

For `j=(κ x).val`, the cut of `b` at `2n+j` is **exactly S**:
vertices of S appear before `2n`; vertices in Z\S all have
original index j and therefore new index `2n+j`; vertices
outside Z have new index at least `3n`. At `2n+j+1` the cut
is **exactly Z**. The inequality j<n separates the last two
cases even if the original index map has unused positions.

## Referee B: closure survives the first reordering

The second frontloading demands that S be closed under the
complete unary operation of the first reordered presentation.
The equality `canonicalValue_frontload_eq` makes this exact,
not merely inclusion of old neighbours. In particular, no
assumption that unrelated components have comparable original
chronological orders has been inserted.

## Referee C: equality alternative is impossible

The frontloading theorem gives “empty or minimal strong” at each
index, not automatic minimality. Since x belongs to the literal
component `Z\S`, x∈Z but x∉S; the two selected cuts cannot
be equal. The minimum-step conclusion follows from the correct
disjunct, not from global strongness or from the rank of x.

## Referee D: ambient graph and predimension are unchanged

Both frontloadings only change the component-index witness.
They do not change G, remove vertices, alter edges or replace
strongness in G by strongness in an induced subgraph. Hence
the derived `IsMinimalStrongStep S Z` is about the **original
ambient graph predimension**.

## Referee E: falsification by exhaustive small cases

The independent regression checks all 76 simple undirected graphs
with at most four vertices and 22,956 finite index assignments.
It retains precisely 1,438 presentations whose nonempty index
steps are minimal strong, and checks 43,792 nested pairs of
closed sets. Among them, **14,859** differ by exactly one
intrinsic component and all passed the exact minimal-strong test.
The prior 2,899 complements of the whole carrier are included.
These are falsification tests, not Lean kernel certificates.

## Referee F: proof and axiom gate

Both the stronger nested theorem and its whole-carrier corollary
are in `CheckC0OneComponentMinimal.lean`. The dedicated
`track-a-one-component-minimal.yml` workflow builds the module,
audits both theorem axioms, scans for placeholders and runs the
finite regression. Main Lean CI also must pass on the exact
committed head. No successful CI result is presumed.

## Application and separate remaining obligations

The result immediately applies to the **finite graph** on a
closed cut Z=Q∪P once finite hereditary presentation has been
transferred to Z with complete unary values intact.
For the countable limit, one still needs a formal transfer from
cofinal exact finite canonical stages, a fair enabled-component
enumeration of order type omega, preservation of all complete
unary values, functional Fraïssé uniqueness, and the representative
convention inside ordered components. None follows from this
finite lemma alone.
