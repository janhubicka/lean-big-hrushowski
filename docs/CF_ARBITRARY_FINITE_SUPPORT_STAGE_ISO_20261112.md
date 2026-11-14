# Track B: arbitrary finite ordered support coordinates

12 November 2026. The theorem composes the now-verified partial
source support-image rigidity and the verified finite-stage
partial order isomorphism. Its source map is an arbitrary
admissible finite map, not the canonical prescribed lift.

## Mathematical claim

For a b-closed finite source s, and a partial map e preserving
the complete b-values, reflecting the birth-level preorder and
preserving the canonical birth order, a new source vertex
v=(n,r,i) has a target w=(m,t,j) with an actual finite-stage
order isomorphism

  {u∈U_n : u∈r.support} ≃o {q∈U_m : q∈t.support}.

The proof uses the complete inclusion of the source support
in s, `birthSupport_eq_stageSupport_image`, exact equality of
the support images from `arbitraryFiniteEmbedding_support_block`,
and `finiteStageSupportOrderIso`. No map of the whole U_n is
constructed or assumed. This remains meaningful for U_0.

## Six adversarial referee roles

1. **Closure and domain:** b-closedness of s ensures *each*
   vertex of r.support is present as its literal old birth
   name. e is evaluated only on members of s.
2. **Exact named support:** the target set is precisely
   t.support, not any isomorphic or supersized old set.
   The support equality is derived from the *complete*
   b-value and the level preorder, not an extra assumption.
3. **Partial order isomorphism:** strict source order is
   the finite-stage order inherited by the canonical birth
   order. The resulting order iso does not require e to be
   total on the old source/target stages.
4. **Empty first support:** no ambient default target
   vertex is chosen. An empty old source support can map
   into the empty target stage U_0.
5. **No hidden local code:** this theorem does not equate
   adjacency matrices or fresh-block ordinals. It supplies
   the OLD coordinate order isomorphism needed by
   `birthRequest_adjacencyCode_eq_of_partialInduced`.
6. **Scope and trust:** only the named endpoint is checked.
   Full finite unique level lifting, restricted composition
   and the embedding-monoid result are not yet obtained.
   No manuscript validation marker is promoted; exact-head
   Lean CI and axiom/source audits are mandatory.

These are internal role-separated adversarial reviews, not
independent human referees.

```sh
lake build BigHrushovski.CFArbitraryFiniteSupportStageIso
lake env lean CheckAxiomsCFTrackBArbitrarySupportStageIso.lean
python3 scripts/check_no_placeholders.py
```
