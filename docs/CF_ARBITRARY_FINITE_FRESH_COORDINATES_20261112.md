# Track B: fresh coordinates of arbitrary finite embeddings

12 November 2026. This composes the exact block-image theorem
and the already verified block-ordinal rigidity for an arbitrary
finite map. The statement is deliberately independent of the
specific prescribed finite lift.

For a full source block B_r, select any source ordinal i and let
e(n,r,i)=(m,t,k). Then for every other source ordinal j in B_r,
the target is (m,t,k_j) with k_j.val=j.val. The target request
t itself is not prescribed in advance; it is recovered from the
exact image of the *whole* block.

## Six independent adversarial review roles

1. **Whole block:** The source b-closedness and exact complete
   b-value preservation give equality of *entire* source and
   target block images. Mere inclusion does not force the
   target request tag on every source ordinal.
2. **No repeated choice:** All source vertices of one r are
   referred to the target of the SAME initial vertex (n,r,i).
   The target tag is recovered as the actual dependent
   StageRequest field of that image, not via an abstract
   isomorphism class.
3. **Level reflection:** The equality of target birth blocks
   uses both directions of the birth-level preorder; an
   order embedding that collapsed levels would not suffice.
4. **Exact fresh ordinals:** The proof invokes arbitrary
   finite ordinal rigidity, which uses the canonical birth
   order and complete block surjectivity. It establishes
   equality of the numerical finite ordinal, not just
   monotonicity or preservation of the first root.
5. **Partial-domain discipline:** e is evaluated only on
   vertices in the source subtype s. Both the chosen initial
   vertex and arbitrary second vertex have explicit
   membership certificates; no ambient global extension
   is assumed.
6. **Remaining gap:** This is the fresh half of the exact
   ordered local coordinate map. The other half is the
   old-support order isomorphism and its pointwise image
   equation. Induced graph equality for all pairs must
   then be composed with the full code theorem. No finite
   uniqueness marker or embedding-monoid claim is made.

Exact-head CI must check the single named endpoint, all standard
axioms and no placeholders. These are internal review roles,
not independent human peer review.

```sh
lake build BigHrushovski.CFArbitraryFiniteFreshCoordinates
lake env lean CheckAxiomsCFTrackBFreshCoordinates.lean
python3 scripts/check_no_placeholders.py
```
