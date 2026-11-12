# Track A — fair canonical stage presentations: adversarial proof audit

12 November 2026. These are seven distinct internal hostile-referee roles, not external human referees.

## Theorem scope

Under the already kernel-certified cofinal exact canonical finite stage certificates, the explicitly defined fair prefixes Q_n are (i) cofinal among finite sets, (ii) given by canonical finite C₀ presentations on the *literal* Q_n with index β_n : Q_n → Fin n and exact complete C-values, and (iii) joined by genuinely minimal strong steps in the original countable graph. All stages are finite, and no empty artificial component is inserted.

1. **Index-cut referee.** For k≤n the old stage of β_n at level k has exact *image* Q_k under Subtype.val. This follows from x∈Q_k iff birth(x)<k; check both implications and the k=0 and n=0 boundaries. Equality of cardinalities alone is insufficient.
2. **Graph-predimension referee.** One must transport the ambient minimal strong step Q_k<Q_(k+1) to the *induced* graph on Q_n via the previously certified `minimalStrongStep_image_iff`. A strong step in N cannot simply be asserted as a new statement on the subtype without this comparison.
3. **Subset referee.** In transporting the step, both stages must be subsets of Q_n, and the finite old-stage inclusion must be established. The case k+1≤n is required; no stage index beyond n is used.
4. **Full-function referee.** The complete C-value agreement is the exact merged theorem `canonicalStages_fairBirthIndex_exact_fullValues` from #427. Local neighbour equality or graph-reduct isomorphism does not replace it.
5. **Cofinality referee.** Singleton exhaustion implies finite-set exhaustion only by finite induction with a common maximum stage and monotonicity. Countability alone is not enough for this specific construction.
6. **Ordering referee.** This constructs the order-ω *sequence of components*, with no choice of a uniform ordered representative inside a component. The paper's ordered expansion and finite-coordinate/Ramsey claims must remain separate.
7. **Formal-trust referee.** Five exact named #print axioms checks, isolated Lean kernel build, whole-source placeholder scan, full repository Lean CI, and an independent exhaustive regression are required before merge. No TeX marker is promoted merely from this conditional theorem.

## Independent regression

Enumerate all finite simple graphs on at most four vertices and component-index maps with empty levels allowed; retain exactly those with empty-or-minimal-strong chronological steps. From each full canonical value operation, run the numerical least-enabled *whole-component* recursion. Check for every initial fair prefix Q_n that β_n indexes its own actual earlier cuts exactly, each induced nonempty step is minimal strong, and the full complete canonical values on Q_n equal the inherited values. A negative control reverses an actual strict dependency and confirms failure of the full function equality. The regression is not the Lean proof.

## Remaining

The canonical **component** enumeration does not choose an actual linear order on individual vertices meeting the uniform local representative convention. A finite-order construction without that convention would be insufficient for the manuscript's ordered expansion. The other open Track A task is the functional Fraïssé extension/homogeneity theorem over *arbitrary* finite closed bases rather than just cofinal stages.
