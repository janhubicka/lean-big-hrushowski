# Track B: complete finite prescribed-level existence

This candidate is stacked on PR #409 and depends on the exact
source-cut canonical equivalence of #408, source-stage recursion
of #406 and source-gap/target-level interfaces of #405.

## Three hostile mathematical checks

**Referee A: no hidden total-stage extension.** The generic
`finiteSourceLiftOfCut` takes a verified map defined on the
actual selected old finite subtype. It never applies that map
to vertices of the full source stage outside the specified
finite source. The equivalence `finiteSourceCutEquiv` is the
canonical actual birth map on an already covering stage.

**Referee B: exact function, inducedness, levels.** The generic
transport proves injectivity, preservation and reflection of
graph adjacency, and equality of the complete literal
birth-b-value after mapping the entire finite restricted
function. The prescribed source map is a SINGLE concrete map
obtained from the stronger birth-aware recursion. Thus the
three requirements refer to the same `f`, not unrelated
existential witnesses. The pointwise target birth identity
is additionally proved for every original source vertex.

**Referee C: no illicit strengthening of the manuscript.**
The theorem currently concerns the concrete birth-labelled
graph equipped with the complete unary birth-b-value. It does
not establish that every arbitrary embedding is the canonical
one, nor the restriction/composition laws or an arbitrary
infinite self-embedding. Recovering full named R/H and
the canonical linear order from these data must be cited or
proved before calling it the full published finite *functional*
embedding. Do not mark the manuscript's finite unique lifting
lemma fully verified yet.

## Mechanical gate

```bash
lake build BigHrushovski.CFCompletePrescribedFiniteLift
lake env lean CheckAxiomsCFTrackBPrescribedExistence.lean
python3 scripts/check_no_placeholders.py
```

Pending exact-head CI and axiom/source audit, no claim of
kernel certification or manuscript validation is made.
