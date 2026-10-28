# Adversarial audit: increasing supports recover literal named support
28 October 2026

The sorted tuple of an actual old support P⊆U determines exactly
the Finset P: membership in the sorted tuple is equivalent to
membership in P. No stronger assumption than equality of the
tuples is needed.

1. Supports are actual subsets of the old stage, not abstract
   isomorphism types of induced support graphs.
2. Sorting by the inherited linear order does not delete or
   merge vertices.
3. Supports of unequal sizes have unequal sorted lists.
4. A proper-prefix relation does not imply equality; the
   theorem is invoked only under full tuple equality.
5. The result does not require a separate isomorphism or
   order equivalence between supports.
6. It handles empty supports without choosing a vertex.
7. The finset extensionality proof is independent of the
   graph, its growth class and any fresh ordinal data.
8. The theorem supplies the named-support part of
   injectivity for complete request codes.
9. The remaining part of code injectivity is equality of
   fresh sizes and full adjacency codes over the now
   *identical* support carrier.
10. Full Lean CI, axiom and placeholder checks are required
    before promoting its marker; no claim about recursive
    countable ordering follows yet.

This is an internal adversarial review with separate roles.
