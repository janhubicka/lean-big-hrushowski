# Track B: adversarial review of arbitrary finite one-block uniqueness

12 November 2026. This is a proposed *arbitrary-map* local uniqueness
theorem, not a statement only about the specially constructed lift.

## Exact statement

Let s be a finite b-closed source. Let e and g be two injective,
induced maps on exactly that finite source, preserving complete
b-values and preserving/reflection of the birth-level preorder and
canonical order. Fix a source vertex v=(n,r,i) in s. If e and g agree
on ALL source vertices born strictly before n and the two image
vertices of v lie in the same target birth stage m, then e(v)=g(v).
Their literal target request tags and fresh ordinal coordinates are
not specified as assumptions.

## Six independent adversarial referee roles

1. **Old support is complete.** The named target-support equality
   is obtained from complete b-values, both directions of the birth
   preorder and agreement on the entire earlier source. It does
   not follow from agreement on a few old neighbours or a total
   old-stage embedding (which need not exist).
2. **Target stage is genuinely fixed.** The images of v are
   explicitly written at the SAME m. It is essential: the same
   local request code is repeated at multiple birth stages, and
   level equality cannot be inferred from structural b-values
   alone. The finite uniqueness induction will supply the
   prescribed level assignment. No global increasing map on ℕ
   is assumed.
3. **Fresh sizes agree.** Each target request has fresh size
   equal to the original source request, by injectivity,
   exact whole-block transport, and the literal cardinality
   theorem. No separate size-equality premise is introduced.
4. **Complete local adjacency matrix.** The full source/target
   codes are equal for EACH map by the kernel-checked arbitrary
   finite code theorem. This includes old–old, old–fresh and
   fresh–fresh pairs and all nonedges. Literal named support,
   fresh size and the whole matrix determine the target request
   record, not only its abstract isomorphism type.
5. **Fresh ordinal is determined.** After the two target tags
   coincide, preservation of the full canonical order and
   complete b-values gives equality of the actual numerical
   fresh ordinal of both image vertices to source ordinal i.
   Therefore the two birth vertices coincide literally.
6. **Induction boundary.** This theorem is one-block only.
   The final uniqueness theorem must derive equality of
   target birth level from a common prescribed represented-level
   assignment, and apply strong induction on source birth
   level, using only the earlier selected source. The empty
   source and target U₀ must remain valid. Restriction,
   composition and the countable monoid require separate
   statements. No manuscript validation marker is promoted
   until the exact-head Lean build, ordinary axiom checks and
   placeholder scans pass.

These roles are internal adversarial analysis, not external human
referee reports.

## Mechanical gate

```sh
lake build BigHrushovski.CFArbitraryFiniteOneBlockUniqueness
lake env lean CheckAxiomsCFTrackBOneBlockUniqueness.lean
python3 scripts/check_no_placeholders.py
```
