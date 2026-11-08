# Track B adversarial audit — exact source b-values on the actual cut

6 November 2026. This is an internal, role-separated adversarial
mathematical audit, not an external referee panel.

## Main integrated assertion

For a finite b-closed source s and ANY actual successor-level
selected carrier (old selected stage cut plus all whole new blocks),
the complete one-level auxiliary b-value of every vertex has image
exactly equal to the source vertex's true countable
`birthBValue` under the canonical source stage-to-birth map.

The proof treats old and new vertices separately:
- OLD: `cutOldBirthBValue` is the exact preimage of the
  complete countable birth value in the selected old subtype;
- NEW: `selectedBlockBValue` comprises the full named old
  support plus EVERY fresh ordinal of its tagged block.

The selected carrier is canonically equivalent to the LITERAL
stage-(n+1) cut.  The image of its full one-level auxiliary
value under that equivalence equals the finite complete
old-value preimage of `birthBValue` on the actual next cut.
The reverse equality is obtained by injectivity of the
canonical stage-to-birth map. Nothing is asserted only
'up to' a chosen isomorphism.

## Hostile referee roles

1. **Source identity:** the equivalence is the verified
   `selectedCutEquiv`, derived from literal selected
   old subsets and full request blocks. No independent
   finite relabelling or unsupported inverse map is chosen.
2. **Old-value exactness:** both s and the complete stage
   image are b-closed. Every old birth value member is
   represented inside the selected old subtype, not
   simply inside the ambient old stage.
3. **Fresh-value exactness:** every named old support
   vertex and every finite fresh ordinal is present.
   Equality is of complete sets, not graph-neighbour
   supports or mere inclusion.
4. **Function-extensionality:** injectivity of the
   stage-to-birth inclusion is explicitly used to
   reflect equality of finite subsets from their
   countable birth images. A noninjective comparison
   would not justify the result.
5. **Empty case:** for empty s or empty first old
   stage the selected carrier has no old vertices;
   the fresh case works over the empty named support.
6. **Circularity:** this bridge uses only previously
   verified b-closed source stage cuts, birth-value
   definitions and the independently checked selected
   fresh identity. The finite unique level-lifting
   theorem is not used.
7. **Induction:** this proves SOURCE representation
   equality. It does not yet imply any target map
   preserves the actual complete b-value. To achieve
   that, instantiate the one-level old value premise
   using `oldBValue_image_iff_birthBValue`, use the
   actual partial batch map's all-vertex theorem,
   and transport through the literal selected-cut
   equivalence.
8. **Uniqueness:** conditional one-level block-code
   rigidity does not imply uniqueness for arbitrary
   functional embeddings without recovering literal
   target support and complete ordered local code.
9. **Kernel:** eight exact declarations are checked
   from a separate `CheckAxiomsCFTrackBBirthAll.lean`
   source, compiled via the CI glob. Full Lean
   build, standard-axiom audit, placeholder scan
   and finite regression suite are mandatory.
10. **Paper:** no manuscript proof or validation
    markers are changed by this PR. The lemma
    `lem:CF-coordinate-pattern` remains partial.

## Subsequent task

Form the actual one-step birth-value equation for an induced
closed old-source map satisfying the explicit old complete
birth-value preservation hypothesis. Then assemble those
equations with the represented-level induction and target
stage ascent, and prove unique lifting for arbitrary
functional embeddings.
