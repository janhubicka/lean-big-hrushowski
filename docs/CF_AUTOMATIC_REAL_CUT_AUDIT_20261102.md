# Track B adversarial audit — actual one-step lift without request assumptions

2 November 2026. The following checks are independent mathematical
review roles, not reports from external human referees.

## Exact result

From an old selected source cut `S=stageCut s n`, an induced,
strictly increasing `e:S→U_m` with *strictly d-closed* image
`e[S] ≤d U_m` produces the unique explicitly constructed
simultaneous request transport. The resulting actual next-cut map
`stageCut s (n+1) → U_(m+1)` is injective, induced (all nonedges
reflected), preserves and reflects the **inherited** order, and
has image strictly d-closed in all of `U_(m+1)`.

The selected request support containment comes from complete
b-closure of the source. Its image support d-closedness follows by
restriction, induced transport and transitivity, NOT as an
additional per-request premise.

## Separate adversarial checks

1. **Partial-source referee:** `e` is defined exactly on the
   selected subtype `S`, not the entire original stage `U_n`.
   `U_n≠∅`, `S=∅`, `U_m=∅` remains admissible; no nonempty
   target assumption is concealed.
2. **Predimension referee:** strictly d-closed *old image* in
   `U_m` remains explicit. Graph inducedness and increasing
   order alone do not imply this; reducing to weak strongness
   would invalidate the support lemma.
3. **Graph referee:** one simultaneous batch is embedded, not
   successive blocks at successive target levels. The cited
   inducedness lemma covers old–fresh, fresh–fresh and distinct
   request blocks including absent edges.
4. **Order referee:** the source/target use the actual inherited
   stage order, not an independently numbered catalogue.
   No requirement `m≥n` or gap between target levels.
5. **Functional referee:** the statement currently packages the
   graph, order and strict closure, but *not* actual birth-block
   auxiliary b-values on the literal source cut. The old-value
   hypothesis and its transport into the actual countable
   `(R,H)` presentation remain separate.
6. **Induction referee:** the step is typed on the genuine
   successor cut; composing steps through nonconsecutive
   represented levels still needs a chosen target-stage
   ascent, with strict d-closed image persistence.
7. **Uniqueness referee:** the formula constructs the
   canonical one-level map. It does NOT show every arbitrary
   functional embedding with this level assignment must
   have its transported local request codes; that premise
   requires intrinsic support/code recovery.
8. **Kernel referee:** three new exact endpoint prints are
   in `CheckAxiomsCFTrackBLevel.lean`. The shared workflow
   discovers it using `CheckAxioms*.lean`, compiles its
   imports and checks the standard axiom allowlist. Require
   full CI and placeholder/regression checks before merging.
9. **Paper referee:** no theorem in the manuscript is
   promoted by this PR. The full finite unique level lift
   and the embedding monoid remain partially formalized.

## Proof economy

This module removes repeated selected-transport certificate
hypotheses from the public one-step lemma. A future proof of
`lem:CF-coordinate-pattern` should invoke this result once for
each represented level, rather than citing separate request
relabelling, selected-batch, order and closure lemmas.
