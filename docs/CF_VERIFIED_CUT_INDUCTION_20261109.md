# Track B: verified finite selected-cut induction interface (9 November 2026)

Based on the fully CI-certified and merged composite one-level lifting
(PR #399) and the earlier empty-cut constructor. The new Lean record
contains an **actual map from the selected source cut**, not a map from
the full source stage. The record asserts exact inducedness, inherited
order, absolute strict d-closedness and complete birth-b-values.

## Adversarial referee panel

**Referee 1 — false strengthening.** A finite `RepresentedLevelPlan`
contains explicit proofs that each source gap has no represented level.
The theorem `RepresentedLevelPlan.lift` therefore proves existence for
a *certified finite sequence of gaps*. It does NOT prove that every
strictly increasing assignment on all represented source levels has
already been converted into such a plan, nor that a final map covers the
entire finite source. Neither implication is stated or used.

**Referee 2 — functional and model-theoretic semantics.** The invariant
is equality of the complete actual `birthBValue` preimages of source
vertices with the entire target value. Closure is in the full target
stage (`IsDClosed _ Finset.univ`), not just the image. It includes
nonedges, not only edge-preservation. The initial empty map remains
well typed if the ambient source stage or the target stage is empty,
and no arbitrary dummy target vertex is introduced.

**Referee 3 — preservation at old and new levels.** The next-step
constructor invokes the proved composite finite gap theorem, not
an unrelated extension lemma. It records separately that old
birth-labelled vertices retain their actual target images and that
fresh vertices are born at exactly the assigned target level. There
is no requirement that the source-stage index map extends to a
strictly increasing endomap of `Nat` (which can fail for level 1 to
level 0). Uniqueness of arbitrary functional embeddings remains open.

## Mechanical gate

Use exact-head Lean and axiom/source checks:

```bash
lake build BigHrushovski.CFVerifiedCutInduction
lake env lean CheckAxiomsCFTrackBInduction.lean
python3 scripts/check_no_placeholders.py
```

Pending exact-head CI, this file is a candidate theorem package and
not yet kernel-certified.
