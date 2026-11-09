# Track B: exact prescribed birth levels

This candidate source is stacked on PR #408, which constructs the
canonical equivalence between a finite source and its full
sufficiently late selected source cut. The new record strengthens
`VerifiedCutMap` with an *explicit* pointwise target birth-level
invariant.

## Adversarial review

**Referee 1 — source and target gaps.** The target birth label
of every previously represented vertex is literally constant
under canonical target ascent. The source gap equivalence is
defined by equality of the actual birth-labelled vertices.
Thus across-gap transport cannot accidentally change either the
source or the target vertex's birth identity. The no-represented-
levels hypothesis on the source interval is necessary.

**Referee 2 — old/fresh split at a represented level.** The
canonical `selectedCutEquiv` decomposes every actual successor
cut vertex into a selected old vertex or a genuinely fresh
tag/ordinal. In the old case, the previous target birth vertex
is unchanged, even when the target stage increases by several
levels. In the fresh case, the canonical one-level lift literally
births that vertex at the assigned target level; it is not
inferred from monotonicity of the target linear order.

**Referee 3 — induction and statement strength.** `assignedTargetStage`
uses target values only at represented source levels and requires
strict increase only on these. The recursion has an empty initial
source and handles unused levels without manufacturing new blocks.
The final theorem transports exact level identities back to the
ORIGINAL finite source subtype. The record's underlying
`VerifiedCutMap` separately retains full inducedness, strict
d-closedness in the whole finite target stage, and complete
birth-b-value equality. The new theorem does not assert uniqueness
among arbitrary embeddings, restriction/composition compatibility,
or the root/support presentation directly.

## Mechanical gate

```sh
lake build BigHrushovski.CFPrescribedBirthLevelLifting
lake env lean CheckAxiomsCFTrackBBirthExact.lean
python3 scripts/check_no_placeholders.py
```

The result is not marked certified until exact-head Lean and
source/axiom validation pass.
