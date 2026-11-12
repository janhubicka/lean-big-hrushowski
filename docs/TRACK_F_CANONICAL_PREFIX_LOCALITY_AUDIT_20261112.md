# Track F — canonical orders depend only on SCC rank prefixes (12 November 2026)

Track F #270, using merged exact assembly and locality results
from #445 and #470. **No manuscript or validation-marker changes.**

## Proposed finite theorems

For a legal ranking r of the actual SCCs, every vertex y in the
complete successor closure C_B of a component B has

\[
   r([y]) \le r(B).
\]

This follows from the intrinsic strict component-precedence
relation and does not assume that every component preceding B
belongs to C_B.

Consequently, when two families of internal SCC orders agree on
all components ranked at most B, their assembled global orders
have identical induced **complete enumerations** on C_B. In
particular the complete directed adjacency-code criterion for
B has the same truth value.

The module \`N0CanonicalPrefixLocality.lean\` packages the full
prefix predicate \`IsCanonicalThroughRank\` and proves that its
truth is unchanged if component orders outside that rank prefix
are modified. This is the chronological dependence required by
the reachable-history induction.

This is a locality theorem, not a counting theorem. The uniform
number of possible next-component orders is not inferred from it.

## Internal adversarial referee panel

1. **Dependency referee.** A proper successor component of B
   must receive a *strictly smaller* legal rank. The rank
   bound fails for illegal rankings; the regression tests
   a source-before-sink ordering of a directed edge.
2. **SCC saturation referee.** If one vertex of an SCC belongs
   to C_B, the entire SCC belongs. The proof uses the
   established successor-closure theorem, not a graph
   connectivity shortcut.
3. **Equality referee.** Agreement of orders is tested on
   actual labelled SCC carriers. The conclusion is equality
   of complete induced enumerations of C_B, stronger than
   an isomorphism or equality of adjacency words.
4. **Outside-referee.** An unrelated SCC may have a smaller
   rank than B without belonging to C_B. It must not alter
   B's canonical criterion; the earlier closure-locality
   theorem supplies this.
5. **Top-component referee.** Agreement *through* B includes
   the current SCC order. Agreement on strictly earlier
   components alone is insufficient to decide the canonical
   predicate of B; the triangle's canonical orders provide
   a negative control.
6. **Prefix-quantifier referee.** \`IsCanonicalThroughRank\`
   checks every component in the prefix, not only the last
   component. The proof transports each check separately.
7. **Certification referee.** Dedicated exact-head Lean
   compilation, standard axiom inspection, placeholder scan
   and an independent finite regression are required. These
   internal checks are not human external peer review.

## Finite regression

The script enumerates all orientations on at most four
vertices (653), all legal SCC rankings, all internal SCC
order choices, and every finite rank prefix. It groups
assignments by the component orders through that prefix
and checks that the inherited closure enumerations and their
complete-code canonicality agree for all assignments within
a group.

Negative controls reject illegal SCC rankings and the
incorrect assertion that changing B's own order leaves its
canonicality unchanged.

## Next proof obligation

To count assignments at a fixed ranking r, let H_i be the set
of reachable choices for the first i SCCs, in r-order.
The prefix-locality lemma proves that the canonicality
condition on an already chosen component does not depend on
future choices. It remains to identify the permitted next
choices from each H_i with the canonical top-component order
fibre over its already ordered lower part P_B. That fibre
has cardinality g_A(B), by merged #473. The reachable-history
product lemma of merged #482 then gives the rank-specific
product and, via #488, the actual finite ordered count.

The infinite N₀ big Ramsey theorem remains separate.
