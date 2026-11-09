# Track B: composite exact C_F lifting through gaps (9 November 2026)

Scope: `BigHrushovski/CFGapThenOneLevelCompleteFunctional.lean`, based on main
`9fb2e481245e25bf11224143e882dfa65592dad5`. The theorem is deliberately conditional on the exact old
birth-`b`-value invariant. It does not assert the full represented-level
induction or uniqueness of arbitrary functional embeddings.

## Mathematical statement

For a finite actual birth-block-closed source `s`, take its selected stage-`n`
cut and a strictly increasing induced embedding `e` into target stage `p`,
whose image is strictly `d`-closed *in the full target stage*. Assume every
source old vertex has **exactly** the target's complete finite birth-`b`-value
as the image of its old value. Let `n ≤ m` be a gap without represented
source levels and let `k` be an arbitrary target-stage gap.

The composite map (source gap, target ascent, actual one-level lift) is
injective, induced including nonedges, preserves and reflects the inherited
stage order, has strictly `d`-closed image in the full target stage
`U_(p+k+1)`, and takes the complete birth-`b`-value of **every** old or
fresh selected vertex onto its complete target value. Consequently the same
equality holds for the literal countable birth-labelled `birthBValue`.

## Independent adversarial checks

**Referee I — construction and source carrier.** The domain remains the
dependent finite subtype `stageCut s (m+1)`, not all vertices of the
source ambient stage. The gap equivalence must use actual canonical birth
labels. The no-represented-level hypothesis is necessary: without it a
source vertex born in `[n,m)` would be absent from the old cut and no
bijection of those cuts could exist. Empty source is allowed; no arbitrary
global increasing map on natural levels is constructed.

**Referee II — predimension and relation.** The premise and conclusion use
`IsDClosed _ Finset.univ` in the *whole* finite target graph, not merely
relative closedness in the selected image. `sourceTargetGapMap_dClosed`
transports the old closed image across target ascent, and
`actualCutLift_completeFunctional` gives absolute strict d-closedness
after the new block. Inducedness is an equivalence on adjacency, not just
forward edge preservation. Stage order is likewise reflected.

**Referee III — complete function and missing theorem.** Full value equality
is not inferred from image inclusion: the gap lemma proves equality of
finite birth-`b`-value sets. `oldBValue_image_iff_birthBValue` converts
it to the *actual countable* birth-value invariant before applying the
one-level theorem, then `stageOldBirthBValue_image` recovers the literal
countable value. The result is an **existence of one canonical composite
map**, not uniqueness among all functional embeddings, and does not yet
iterate over every represented source level nor identify the final finite
functional source with an arbitrary published finite structure.

## Mechanical validation

Independent imports and exact axiom endpoints:
`CheckAxiomsCFTrackBGapComplete.lean`.

Run:

```sh
lake build BigHrushovski.CFGapThenOneLevelCompleteFunctional
lake env lean CheckAxiomsCFTrackBGapComplete.lean
python3 scripts/check_no_placeholders.py
```

These checks are required on the **PR head**. Until Lean and the
source/axiom audits pass, this is a proposed (not kernel-certified) proof.
