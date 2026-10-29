# Adversarial audit: exact order and uniqueness of constructed C_F requests

29 October 2026

## Claim

The actual target request built by transportGrowthStageRequest
satisfies the complete RequestCodeTransportOn certificate.
The equality of the full ordered adjacency matrix is a proved
conclusion of the preceding module, not a hypothesis.

For any two source requests supported inside the selected old
source S, provided their literal target support images are
strictly d-closed and their old induced graphs are preserved,
the target requests are distinct whenever the source requests
are distinct. Their exact lexicographic order is preserved
and reflected, including proper-prefix support comparisons.

## Hostile checks

1. **Existence and uniqueness.** Existence is supplied by the
   actual bounded target request construction, not by an
   abstract isomorphism class. Uniqueness uses injectivity of
   the complete key (literal named support, fresh size and
   all ordered adjacency bits). No extra uniqueness
   assumption is inserted.

2. **Order.** The map f need only be strictly increasing on
   the selected old source S. The source and target stages
   can have different sizes, and no whole-stage embedding
   is assumed. Proper-prefix comparisons are preserved by
   the earlier partial-source lex theorem.

3. **Predimension.** Each target support Q=f[P] must be
   strictly d-closed in the entire target old stage.
   This hypothesis is not inferred from order alone.
   In the finite lifting application it comes from the
   selected b-closed old image and the previously verified
   strict d-closure transfer.

4. **Graph.** The target local graph is the named-base
   pullback of the source local graph, with fresh ordinals
   fixed. The full adjacency matrix equality, including
   reflection of all nonedges, is a theorem of the
   preceding code-transport module.

5. **Lean and dependency audit.** Four exact theorem
   endpoints are registered in CheckAxioms.lean. CI must
   compile the whole import graph, audit standard axioms,
   scan for placeholders and run all finite regressions.
   The theorem must not depend on an unfinished draft
   theorem about simultaneous block assembly.

## Remaining gap

The simultaneous map of all selected same-level blocks
has not yet been assembled. The request map is injective
and order-preserving, but a complete finite lift also
needs the induced graph on the old source plus every
selected block, the exact old-fresh boundary, absence
of cross-block edges, d-closedness of the selected batch,
and preservation of the functional closure operations.
The embedding-monoid theorem is downstream.

These are role-separated internal adversarial checks,
not independent external human referee reports.
