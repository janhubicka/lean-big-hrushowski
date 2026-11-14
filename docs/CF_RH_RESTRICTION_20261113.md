# Track B: R,H restriction compatibility of finite prescribed lifts

13 November 2026. This corollary is stacked on finite R,H
composition PR #521 and uses the already merged b-restriction
compatibility PR #499.

## Exact result

For s⊆t finite b-closed source structures, choose a target
level assignment strictly increasing only on the represented
levels of t. The literal restriction of the constructed
prescribed lift of t to s agrees with the independently
constructed prescribed lift of s, even with different stage
covers. The restricted lift therefore preserves full root
values R(v), all H-values defined on finite sets of roots,
and reflects the domain of H.

## Adversarial referee roles (internal, not human)

1. **Partiality:** Restriction is on the literal finite
   subtype s, not an extension to any total source stage.
2. **Closure:** Both s and t are genuinely b-closed, so
   complete b-values commute with literal inclusion.
3. **Stage choices:** The two finite stage covers are
   independent; their equality follows from arbitrary-map
   uniqueness, not identical recursive source stages.
4. **Levels:** Strictness on represented levels descends to
   s; no global increasing map on ℕ is assumed.
5. **Partial function:** H-domain reflection is part of the
   imported R,H predicate, not inferred from preserving H
   wherever defined.
6. **Scope:** This is still only a finite statement. The
   paper's countable self-embedding and embedding-monoid
   conclusions remain unchecked in this branch.

## Required CI gates

```sh
lake build BigHrushovski.CFPrescribedFiniteRHRestriction
lake env lean CheckAxiomsCFTrackBRHRestriction.lean
python3 scripts/check_no_placeholders.py
```

The full stack must pass exact-head kernel and standard axiom
checks before merge or upgrading any TeX validation marker.
