# Adversarial review: the chosen order and C_F root preservation
26 October 2026

## Precise mathematical statement

Fix any strict binary relation < on the actual tagged C_F birth carrier whose restriction to each complete birth block agrees with the finite order on its local fresh-ordinal labels. The manuscript chooses its global linear order by ordering levels, ordering the finite collection of requests at each level, and ordering vertices inside each request block by their chosen finite order. **Only the last property is used in the root-recovery equivalence.**

An induced injective embedding of any b-closed source X (empty, finite, or infinite), preserving/refecting the birth-level preorder and preserving the chosen strict relation < on X, preserves complete b-values exactly if and only if it preserves complete R- and defined H-values, with preservation/reflection of the partial H-domain on finite source arguments. No extra embedding hypothesis about the internal ordinal labels is necessary: it follows from the complete b-value image, top-block reconstruction and the chosen-order compatibility. The proof works for a literal source subtype map and never requires a globally induced extension.

## Ten role-separated adversarial checks

1. **The chosen order is a premise, not fabricated.** The theorem is conditional on `BirthBlockOrderCompatible`. Constructing the precise manuscript order on the countable Lean carrier, and verifying this property there, remains a separate small but essential integration task.
2. **Only intra-block comparisons.** The proof never compares different request blocks with the chosen order; any reordering of requests within a level leaves the root-recovery argument unchanged.
3. **Whole-block images.** Deriving the internal order condition requires exact image equality for the *complete* block, obtained from b-value preservation and reflected level equality. Without full block images, a first-vertex argument can fail.
4. **Reflection of level preorder.** The target preimage of a top-level vertex can be shown to belong to the source top block only if both directions of the level preorder are preserved.
5. **Target membership.** Before using order compatibility at the target, both images are explicitly shown to lie in the complete target block. Merely knowing the images have equal birth levels would not suffice.
6. **First-root reflection.** On the forward b-preserving implication, injectivity on X turns root commutation into reflection of root status, needed for the partial H-domain. On the reverse implication, root commutation is not an extra hypothesis.
7. **Order independence of reverse direction.** R/H-to-b value recovery uses induced adjacency, reflected levels and complete values, but no fresh-ordinal order. The proof does not circularly derive b-value preservation by using an order premise that itself depends on b-values.
8. **Empty source.** The literal source map may have the empty domain. The identity-outside-X extension is well-typed with no chosen source element; all arguments are valid for the empty source.
9. **Finite function domains.** The H-value statement is quantified only over finite root sets in X, and domain reflection refers only to finite sets in the source image, not all ambient root sets.
10. **Kernel and editorial status.** Three theorem endpoints must pass full Lean build and exact axiom/no-placeholder audits. Even if they pass, a GREEN marker for the *exact manuscript order* must await the separate concrete order construction, or a direct theorem identifying that order with the compatible relation.

These are independent internal adversarial mathematical reviews, not external human referees.
