# Track B: whole finite source lift from arbitrary represented levels

The construction is stacked on PR #406 and uses exactly the proven
`VerifiedCutMap` on the actual finite stage cut.

## Three adversarial referees

**Referee 1: source identity.** A finite source `s` is a literal
subset of the countable birth carrier. It sits inside some finite
stage because each of its vertices has a finite birth index.
The canonical `finiteSourceCutEquiv` is forced by the injective
stage-to-birth map, not an arbitrary graph-copy isomorphism.
Its image is all of `s` at any sufficiently late stage.

**Referee 2: complete functionality.** The source is assumed
`IsBirthBlockClosed`: this means the entire actual birth-b-value
of every source vertex lies in `s`. Restriction of the unary
operation to the finite source is thus defined as the full
finite preimage on its subtype. `finiteSourceLift_birthBValues`
asserts **set equality**, not support inclusion, and its proof
transports the exact selected-cut b-value through the literal
source-cut equivalence. This permits only finite b-closed
sources; no arbitrary finite induced subset is silently treated
as a substructure.

**Referee 3: logical scope.** The theorem produces an injective
induced graph map on all vertices of a finite b-closed source
and proves complete unary birth-b-value transport. It does NOT
yet prove that each original vertex has target birth level
`h(v.birth)`; this requires tracking the old and fresh labels
in the stage recursion. Nor does this by itself prove uniqueness,
the entire `R,H` presentation, order reflection, restriction or
composition compatibility. The missing conditions must not be
silently inferred from injectivity and b-value equality.

## Verification gate

```bash
lake build BigHrushovski.CFFiniteSourceLevelLifting
lake env lean CheckAxiomsCFTrackBWholeSource.lean
python3 scripts/check_no_placeholders.py
```

This is a candidate, not a certified result until the exact
stacked head passes kernel, axiom and source audit.
