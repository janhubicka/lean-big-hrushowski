# Track B hostile audit: recover both support and block by their birth levels

8 November 2026. Internal role-separated adversarial checks, not independent human referee reports.

## Statement

For a genuinely partial map on a selected finite C_F source, suppose
(1) the COMPLETE b-value of a source fresh vertex maps ONTO the complete
target b-value, (2) every source old-support vertex maps to a target
vertex born STRICTLY BEFORE m, and (3) each source fresh-block vertex
maps to a vertex born at EXACTLY m. Then the partial map sends the
complete old support ONTO the target old support, and the complete
fresh block ONTO the target fresh block.

This refines the separate-support theorem of #373: **the entire block
image is a CONCLUSION rather than an independent assumption.**
It additionally removes the need for injectivity in the partition
step, though actual embeddings will of course be injective.

## Adversarial referee roles

1. **Set-theoretic referee:** equality of the whole union image alone
   does not force equality of either part. The label dichotomy is essential.
2. **Old/new referee:** each source old-support image has birth label <m;
   every target old support vertex has birth label <m.
3. **Fresh referee:** each source fresh-block image has birth label m;
   every target fresh-block vertex has birth label m.
4. **Onto referee:** both separate equalities, not just inclusions,
   follow by taking preimages in the complete union image equality.
5. **Partial-source referee:** the map is defined ONLY on the finite
   subtype s; no invented global self-map is introduced.
6. **Injectivity referee:** no injectivity is used in this partition
   argument. Omitting it here does not assert arbitrary non-injective
   maps are embeddings.
7. **Closure referee:** b-closedness of s is NOT used for the elementary
   partition argument once complete selected-source value transport
   is already a premise. Proving that premise from a functional
   embedding generally does require its b-closed domain.
8. **Scope referee:** the old/new level hypotheses are explicit. In
   particular, the claim DOES NOT infer level preservation from
   graph inducedness, nor establish arbitrary functional uniqueness.
9. **Reusable core:** the finite-set partition theorem is independent
   of graph theory and usable for C_0 component images as well.
10. **Lean referee:** exactly two independent axiom endpoints;
    verify complete CI and inspect any unresolved Lean elaboration
    errors before merging or changing manuscript validation marks.

No frozen manuscript prose or green validation marker is changed.
