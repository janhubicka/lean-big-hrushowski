# Track B: finite unique lifting in the actual R/H language

12 November 2026 — stacked on PR #481. Draft until the entire stack
passes exact-head Lean CI and standard-axiom/source audits.

## Statement

For a finite b-closed source s, two arbitrary embeddings e,g into
the actual countable C_F birth structure preserve and reflect graph
adjacency, the birth-level preorder and the canonical order, and
preserve the R operation and every defined H-value while also
reflecting the partial domain of H. If both maps have the SAME target
birth level for each source vertex, then they are the SAME map.

This is uniqueness for the original (R,H) functional language,
not merely for the auxiliary b-presentation. The finite existence
theorem is already separately verified.

## Six adversarial referee roles

1. **Arbitrary maps, not the canonical witness.** The inputs
   e,g are unrestricted finite source subtype maps satisfying
   the embedding conditions. The theorem does not identify
   either of them with the constructed lift by assumption.
2. **Partial H domain.** In addition to preservation of
   each defined H-value, the hypotheses include the reverse
   condition that a target image finite set lies in the
   domain of H iff the source set does. Without reflection
   the established b↔R/H equivalence would not apply.
3. **The whole R operation.** R-values are preserved exactly,
   as full images, not only pointwise root predicates.
   This is needed for full complete b-value preservation.
4. **Domain-local equivalence.** The b↔R/H equivalence
   requires the source subset to be closed under b and
   the maps to be injective, induced, birth-level-preorder
   preserving and canonically ordered. The theorem lists
   every one of these conditions and does not assert
   anything about maps outside s. Their extension outside
   s is only a device for evaluating ambient finite-set
   operations.
5. **Exact represented levels.** The prescribed level
   assignment is compared only at the birth levels of
   vertices in s. No globally increasing map on all ℕ is
   required, allowing source gaps, target gaps, empty
   s, and the first represented source level to map to 0.
6. **Verification and paper scope.** This is a one-line
   transfer from the auxiliary finite uniqueness theorem,
   but the transfer theorem and ALL of its dependencies
   must pass an exact-head kernel and standard-axiom check.
   Existence plus uniqueness will then prove finite
   unique level lifting. Restriction/composition and the
   countable embedding monoid still require explicit
   proofs before claiming the whole manuscript subsection
   validated. No validation marker is promoted here.

These are internal adversarial review roles, not outside
peer review.

## Exact gate

```sh
lake build BigHrushovski.CFArbitraryFiniteRHUniqueness
lake env lean CheckAxiomsCFTrackBRHUniqueness.lean
python3 scripts/check_no_placeholders.py
```
