# Track B: arbitrary finite R/H restriction and composition

14 November 2026. Follow-up to the exact-head certified finite
substructure theorem (PR #537) and intrinsic-recognition theorem
(PR #546). This is the remaining compatibility endpoint stated
in Section 3b of the manuscript, not a new countable construction.

## The two finite assertions

1. **Composition**: given a finite genuine R/H-substructure s,
   an arbitrary induced ordered R/H embedding e on s, and an
   arbitrary such embedding g **defined exactly on e[s]**,
   the map g∘e is again an embedding of the actual ordered R/H
   language. It preserves the complete R-values, defined partial
   H-values, and reflects H's partial domain. It preserves
   and reflects nonedges, the canonical strict order, and
   the birth-level preorder. The intermediate image is actually
   R/H-closed, not a casually selected graph-induced image.
2. **Restriction**: given finite genuine R/H-substructures s⊆t
   and an arbitrary ordered R/H embedding on t, its literal
   restriction to s is again an R/H embedding, including the
   *full partial H-domain reflection*. It is not assumed that
   the original map was one of the constructed finite lifts.

For either result, its target-level assignment is determined
intrinsically by the resulting map, and needs to be strictly
increasing only on levels represented by the source.

## Adversarial referee panel (six internal roles)

- **Partial function and language referee.** Passing only
  graph-inducedness is insufficient. Both original maps
  preserve complete R-values and H-values, *and reflect
  the domain of H*. The conclusion uses the actual
  `FiniteRHLevelEmbedding` predicate, not merely b-values.
- **Finite-image referee.** Composition's intermediate
  carrier is the literal finite image e[s], not a full
  source or target stage. It is b-closed because the exact
  R/H-to-b translation and complete b-image equality imply
  b-closure, and hence R/H-closed by the recovery theorem.
- **Order referee.** The birth-level preorder and actual
  canonical strict order are both reflected and preserved.
  Dropping the latter could permit permutations of fresh
  ordinals inside a block; neither is inferred from
  graph adjacency alone.
- **Restriction referee.** The starting embedding may be
  *arbitrary*. Its equality with the canonical lift for
  its intrinsic level map is the already kernel-checked
  PR #546 theorem; only then is the previously merged
  finite restriction identity applied.
- **Level-gap referee.** Both statements include empty
  sources, missing source/target levels, and maps whose
  first represented source level is sent to target level
  zero. No global increasing self-map of ℕ or total
  old-stage extension is assumed.
- **Proof-trust/referee of circularity.** Composition
  uses the merged genuine partial b-composition theorem
  (#509) plus finite arbitrary-map uniqueness to recover
  the partial R/H properties of the composite. Restriction
  uses finite recognition (#546) and restriction of the
  canonical lift (#527). Neither argument uses the
  countable monoid statement or an unproved Ramsey-space
  theorem. Two exact #print axioms gates guard the new
  conclusions.

These are independent *mathematical challenge roles* in one
internal adversarial audit, not reports from external reviewers.

## Verification

```sh
lake build BigHrushovski.CFArbitraryFiniteRHCompatibility
lake env lean CheckAxiomsCFTrackBArbitraryRHCompatibility.lean
python3 scripts/check_no_placeholders.py
```

Require exact-head Lean CI (including the standard-axiom
audit and finite regressions) before merge or promotion
of any manuscript verification markers.

## Scope

These results complete the finite closure of the *actual*
ordered R/H embedding class under restriction and
composition. They do not identify the monoid of countable
self-embeddings with increasing maps of ω, or establish
any Ellentuck-space axiom. The countable argument remains
in Track E.
