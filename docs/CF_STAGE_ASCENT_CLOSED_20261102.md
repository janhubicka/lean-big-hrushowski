# Track B: adversarial audit of C_F target stage ascent

2 November 2026. These checks are role-separated internal
mathematical reviews, not reports from external human referees.

## Statement

For each finite tower stage U_n and natural k, the canonical old
inclusion `ascend n k : U_n→U_(n+k)` has strictly d-closed image.
Consequently any finite `A ≤d U_n` has
`ascend[A] ≤d U_(n+k)`. For a selected-source map
`e:S→U_n` with `e[S] ≤d U_n`, the image under ascent is
strictly d-closed in the **whole** later stage. The map also
retains complete graph inducedness and the actual inherited
order by already formalized exact stage-ascent equivalences.

## Hostile referee roles

1. **Strictness:** all closure assertions use
   `Predimension.IsDClosed` and its *strict* transitivity, not
   `IsStrong`. At successor steps the old tagged part is
   strictly d-closed in the entire new tagged graph.
2. **Induction base:** k=0 uses identity inclusion and reflexive
   d-closedness. The proof must not require the stage to be
   nonempty.
3. **Induction successor:** the current image is closed in the
   old summand, and the entire old summand is closed in the
   new stage; transitivity is applied in the correct direction.
4. **Transport:** induced predimension invariance is used only
   over the image of a finite induced injection, *not* to
   assert closure in a larger host without a stage-closure
   premise.
5. **Literal labels:** all maps are canonical iterations of
   Sum.inl, not separately chosen copies or arbitrary
   graph isomorphisms.
6. **Partial domain:** the old map is defined only on selected
   source vertices S; no total map of the original old stage
   into the target old stage is needed.
7. **Order:** exact `stageLt_ascend_iff` gives both directions
   of strict-order comparison, including when the target stage
   is not adjacent.
8. **No false ω-extension:** arbitrary finite target gaps are
   allowed, but this module does not create an increasing
   self-map of all ω or assume that a finite assignment extends.
9. **Known gap:** the represented-level induction still needs
   to transport *complete b-values* of old vertices through
   stage ascent and prove uniqueness for arbitrary embeddings.
   These theorems do not discharge those obligations.
10. **Kernel:** five exact axiom endpoints are listed in the
    separate `CheckAxiomsCFTrackBAscent.lean`. The glob-based
    workflow (merged PR #310) must compile this source and
    pass exact axiom, placeholder and finite regression checks
    before the results can be called machine-verified.

No manuscript mathematical prose or green markers are changed
by this PR.

## Additional exact b-value check (2 November 2026)

The canonical old-stage ascent preserves the LITERAL birth label
(`toVertex_ascend`, already kernel-checked). Hence applying the
actual complete auxiliary `birthBValue` to that vertex gives
the same complete finite set of birth-labelled vertices, with
no loss of old support or part of a fresh block. The new
`birthBValue_ascend_exact` theorem records this consequence.

This proves persistence of the target birth-b-value itself,
not yet preservation of complete b-values by the transported
source embedding. That latter equality remains an induction
premise and must be propagated through the actual source-cut
one-level map.

The new endpoint is listed in the standalone axiom audit and
requires successful full CI before any green marker.
