# Track F: component-rank prefix audit (1 November 2026)

Scope: a small independent proof branch off Track F PR #270, not a claim
that the infinite N₀ Ramsey theorem is complete.

The finite SCC dependency relation is already defined and certified in
\`OrientationComponentOrder.lean\`. The new conditional interface takes a
rank function on the *actual* component vertex sets satisfying
\`ComponentPrecedes B C → rank B < rank C\`. It proves for every cutoff:

1. Every SCC is either entirely selected or entirely omitted.
2. The selected vertex set is successor-closed.
3. The selected vertex set is strong for the undirected graph predimension.

The proof applies the existing SCC-downset characterization, not a new
orientation counting argument. No injectivity of rank is required; equal
ranks are allowed only for incomparable components. For actual linear
extensions, injective consecutive ranks will be a separate property.

**Adversarial checks:** Exhaustive finite orientation check through four
vertices verifies 1,586 component rankings and 7,423 closed rank prefixes
across 653 orientations. Reversing the dependency on one oriented edge
makes the claimed closure fail. Directed SCC cycles are collapsed to
one component first. The empty orientation and the empty rank prefix
are included.

Machine certification requires a successful isolated Lean build and
standard-axiom/placeholder audit. The result does not count permitted
local orders or prove a big Ramsey degree.
