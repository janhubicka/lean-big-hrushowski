# Track B adversarial audit: actual source-cut gap equivalence

8 November 2026. The roles below are a mathematical adversarial
check, not reports from independent outside human referees.

## Claimed result

For any finite source s and n≤m with no represented birth level of
s in [n,m), the stage-n and stage-m cuts have identical birth images.
Using the verified injectivity of each stage-to-birth map, this equality
determines a canonical bijection of the literal dependent cut subtypes.

The bijection preserves every actual birth label, the complete induced
graph including nonedges, and the inherited finite-stage order. No
abstract graph copy, target-level assignment or enumeration is chosen.

## Role-separated hostile checks

1. **Gaps.** The excluded interval is [n,m), not [n,m].
   A vertex born at m is in neither stage cut and must not be
   spuriously added by the map.
2. **Empty source.** The subtype can be empty while the ambient U_n
   is nonempty. All maps and the equivalence remain defined.
3. **No totalization.** A selected old-cut map is NOT a function
   on all of U_n. The equivalence is between precisely the two
   cut subtypes; no arbitrary ambient stage embedding is used.
4. **Literal identity.** The chosen target representative is forced
   by equality of countable birth labels and injectivity of
   toVertex. Classical choice never selects a different image
   or changes block ordinals.
5. **Surjectivity.** The reverse image equality ensures that
   every target-cut vertex has a source-cut representative. Merely
   having a forward inclusion would not suffice.
6. **Graph.** Inducedness at both stages is reflected through the
   common countable graph. Nonedges, old/new boundary pairs and
   distinct blocks are included.
7. **Order.** Both stage orders are the canonical restrictions
   of the SAME countable birth order. An arbitrary local order
   on request copies would not justify this assertion.
8. **Functional values.** The result does not itself prove that
   complete b-values are preserved by an arbitrary map. Its
   literal birth identity is the source-cut contribution to
   that separate induction invariant.
9. **No false omega extension.** A finite assignment of
   represented levels need not extend to a strictly increasing
   endomap of all natural numbers. The proof imposes none.
10. **Kernel.** Nine exact endpoints are in the standalone
    CheckAxiomsCFTrackBGapEquiv.lean file, read by the current
    workflow. Full CI (Lean build, standard axiom and
    placeholder audits, all finite regressions) is mandatory
    before merge or green manuscript citation.

This is a SOURCE-gap equivalence only. Strict d-closedness of the
target image under target ascent is independently certified.
The complete finite unique lifting induction, arbitrary-embedding
uniqueness and embedding monoid remain unfinished.
