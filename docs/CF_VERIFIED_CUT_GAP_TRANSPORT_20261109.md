# Track B: source gaps and exact prescribed target levels (9 November 2026)

Source: `BigHrushovski/CFVerifiedCutGapTransport.lean`. This is a
proof-interface refinement of merged PR #401; no change to the
manuscript's currently frozen statements.

### Independent adversarial referee reports

**Referee 1 (finite source and domains).** The source transport is an
equivalence between the **actual** selected finite subtype at stage
`n` and the subtype at stage `m`, provided there is no represented
level in `[n,m)`. This hypothesis is indispensable. The theorem does
not totalize the map to the whole source stage. Every operation is
defined on a genuine selected cut, including empty cuts.

**Referee 2 (predimension and the unary function).** Absolute strict
d-closedness in the entire target finite stage is preserved across the
gap. The old complete birth-b-value is carried *onto* the full target
value, not included in it. Graph adjacency and nonadjacency are both
preserved and reflected. The old vertex's literal birth identity is
unchanged after any canonical target ascent.

**Referee 3 (level arithmetics and completeness).** For a prescribed new
target level `q` and current old stage `p`, exactly `p≤q` is needed:
`p+(q-p)=q`. This permits consecutive target levels; it does not add
an artificial separation condition. New vertex images are born exactly
at `q`, while old vertices retain previously assigned levels. None
of these interfaces proves that *every* increasing finite level
assignment has already been converted into a finite plan, or that
the arbitrary-embedding uniqueness half is complete.

### Exact-head checks

```bash
lake build BigHrushovski.CFVerifiedCutGapTransport
lake env lean CheckAxiomsCFTrackBGapTransport.lean
python3 scripts/check_no_placeholders.py
```

Mark as proved only when the exact-head GitHub Actions Lean job, axiom
audit, source audit, and independent review all pass.
