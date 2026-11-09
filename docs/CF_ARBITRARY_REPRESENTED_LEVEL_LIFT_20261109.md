# Track B: arbitrary increasing finite represented-level assignments

Candidate stacked on PR #405 (verified source-gap and prescribed-target
interfaces). All proof terms work on the ACTUAL finite selected-cut
subtypes and the exact target stages.

## Independent adversarial referee panel

**Referee 1 — level assignment.** The source finite represented levels
are exactly `representedLevels F K s`. Strict increase is assumed
only on pairs in that finite set. The prescribed map is an arbitrary
function `h : ℕ → ℕ` with *no constraint at unrepresented levels*;
its values there are never used. For example, assigning source level
1 to target level 0 is admitted: the first source cut is empty and
the first represented block is born in target stage 0. This case
cannot arise from a strictly increasing self-map of ℕ.

**Referee 2 — induction and target-stage bound.** Before a source level
`n`, `assignedTargetStage` is zero if none was previously represented,
and otherwise one more than the target level of the latest represented
source level. The crucial estimate
`assignedTargetStage n ≤ h n` at represented `n`
uses strict increase between represented indices only. If `n` is
unrepresented, the source cut changes only via the canonical
gap equivalence; no new block is inserted, and the target stage
does not move. If `n` is represented, the one-level constructor
places the whole fresh block at `h n`, irrespective of the values
of `h` at unused source levels.

**Referee 3 — all relational and functional data.** The inductive
invariant is a genuinely partial map on the literal selected cut;
injectivity, adjacency and nonadjacency, inherited linear order,
strict d-closedness in the WHOLE target stage and equality of the
COMPLETE actual birth-b-value are preserved. This is an **existence**
construction. Uniqueness of arbitrary functional embeddings, the
inverse range inclusion in Section 6, and a globally increasing
level endomorphism are not claimed. To obtain an embedding on a
specified finite source, one must still identify it with the
selected cut after a stage beyond its finitely many birth levels.

## Mechanical gate

```bash
lake build BigHrushovski.CFArbitraryRepresentedLevelLift
lake env lean CheckAxiomsCFTrackBArbitrary.lean
python3 scripts/check_no_placeholders.py
```

This is a candidate proof until exact-head CI plus source/axiom audits
pass; do not prematurely upgrade manuscript markers.
