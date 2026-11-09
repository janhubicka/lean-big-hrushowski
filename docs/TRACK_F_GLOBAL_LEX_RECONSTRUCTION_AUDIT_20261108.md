# Track F — reconstructing finite labelled lexicographic orders (8 November 2026)

Stacked on draft PR #353 (global lexicographic component-interval orders),
itself stacked on Track F integration PR #270. No manuscript edits or
validation-marker promotions.

## Exact finite statements

For the actual SCC rank function and arbitrary local numeric vertex
ranks, the induced relation is exactly the lexicographic comparison of
(component rank, local rank). If two vertices are in different SCCs,
the truth of x<y depends **only** on the component ranks. Within one
SCC it depends **only** on local rank comparison.

The final theorem gives an if-and-only-if: two such complete labelled
order relations are identical precisely when their comparisons between
different SCCs agree and their comparisons inside each SCC agree.
The theorem does not identify arbitrary numerical local ranks, which
may differ by increasing reparametrization, nor claim they are the
canonical least adjacency-code choices.

## Separate adversarial review roles

1. **SCC referee:** use actual mutual directed reachability, not weak
   connected components; directed cycles are single SCCs.
2. **Rank referee:** a ranking is a bijection on the genuine SCC type;
   injectivity is essential to exclude tied ranks for different SCCs.
3. **Local referee:** local rank values need not be globally injective;
   equality of their induced *comparisons*, not their numbers, is used.
4. **Reconstruction referee:** comparisons are split into disjoint
   different-SCC and same-SCC cases, including x=y and the empty graph.
5. **Order referee:** the lemma compares actual labelled strict order
   relations, not quotient sets of unlabelled isomorphism types.
6. **Scope referee:** the abstract locally injective ranks remain
   unconnected to the exact minimum complete adjacency-code rule;
   counting genuinely permitted global orders and the infinite Ramsey
   theorem are still open.

Kernel endpoints and placeholders are audited in
\`CheckTrackFGlobalLexReconstructionAxioms.lean\`; independent tests
exhaust all two-orientations on at most four labelled vertices with
legal rankings and two locally injective rank assignments. This is
not certification until exact-head GitHub Actions succeeds.
