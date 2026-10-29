# Adversarial audit: complete code of an actual transported C_F request

29 October 2026

## Claim

The target StageRequest constructed from an actual named support
image has the same fresh ordinal size and exactly the same
complete ordered adjacency matrix as the source StageRequest.
The graph of the target local code is the named-base pullback
of the source local graph, fixing each fresh Fin ordinal.

## Hostile checks

1. **Graph referee.** The proof uses induced adjacency
   equivalence, not only a graph homomorphism. All old-old,
   old-fresh and fresh-fresh pairs and all nonedges are
   preserved by the named-base pullback.

2. **Coordinate referee.** The support is transported by an
   order isomorphism; the fresh Fin interval is fixed by the
   identity order isomorphism. Thus the sorted complete
   coordinate lists are mapped exactly. A non-order-preserving
   permutation of the old support would change the matrix.

3. **Finite request referee.** The theorem concerns the actual
   dependent StageRequest produced by the preceding
   transportGrowthStageRequest definition. It does not
   assume equality of the target adjacency code; that
   equality is the conclusion. The target request exists
   only when its literal support is strictly d-closed in
   the target old stage.

4. **Lean referee.** Four exact axiom endpoints are registered
   and require a successful full CI run. The dependent
   equality between the constructed request's code and
   the named-base pullback graph must be checked by the
   kernel, not asserted by an unverified cast.

5. **Amalgamation referee.** This does not yet construct the
   simultaneous map of all selected blocks at one level.
   Once code equality is verified, the existing
   requestCodeTransportOn_of_namedImage,
   requestLexLt_transportOn_iff and
   requestCodeTransportOn_reflects_eq theorems can supply
   exact order comparison and noncollision.

These are role-separated adversarial mathematical checks
within the project, not external human referee reports.
