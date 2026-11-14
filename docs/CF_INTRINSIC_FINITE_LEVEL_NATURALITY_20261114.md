# Track B: intrinsic finite-level restriction and composition

14 November 2026, independent of the still-unverified
arbitrary-R/H compatibility PR #564.

## Mathematical statements

For any finite source map reflecting the birth-level preorder,
the target level of a represented source level is well-defined
independently of the choice of source vertex.

1. If s⊆t, the level assignment extracted from the
   literal restriction of a map on t is precisely the
   restriction of the original level assignment to the
   levels represented in s.
2. If g is defined on the **literal image e[s]**, the
   assignment of g∘e on the levels represented in s
   is the composition of the assignments of e and g.
3. In particular, this composite assignment is strictly
   increasing on exactly the levels represented in s.

No graph, b-operation, R/H function, or closure assumption
is necessary. These are pure finite-level results, and
do not assert anything about unrepresented levels or
countable self-embeddings.

## Internal adversarial referee panel

- **Representative-choice referee.** Equality on represented
  levels comes from the proved
  `finiteEmbeddingLevelMap_exact` and
  `finiteEmbeddingLevelMap_unique_on_represented`, not
  a reliance on the classical witness chosen by the
  definition being consistent with arbitrary maps.
- **Partial-domain referee.** The second map is typed
  precisely on e[s], and its input `j x` is the
  literal image subtype. No extension to a complete
  old stage is postulated.
- **Order referee.** Both maps must preserve and reflect
  the level preorder. Mere monotonicity is insufficient
  for the level-map assignment to be well-defined on
  whole source level classes.
- **Gap referee.** All equalities hold only at birth
  levels represented in s. At an absent level the
  `finiteEmbeddingLevelMap` convention returns zero;
  no global composition law or monotonicity is claimed.
  Empty sources are covered vacuously.
- **Value/graph referee.** No preservation of a graph
  edge, b-value, R or partial H is used. This makes
  the lemma applicable in both the finite graph and
  the ordered functional setting, and avoids a
  circular dependence on Track E's countable gluing.
- **Proof-trust referee.** Every endpoint has an exact
  `#print axioms` check, and CI builds all modules,
  runs the placeholder scanner and finite regression
  suite. The source adds no axioms or admitted proofs.
  Theorems are draft-only until exact-head CI passes.

Six separate internal mathematical challenge roles,
not external human referee reports.

## Verification

```sh
lake build BigHrushovski.CFFiniteIntrinsicLevelNaturality
lake env lean CheckAxiomsCFTrackBIntrinsicLevelNaturality.lean
python3 scripts/check_no_placeholders.py
```

These results can be reused in the countable monoid
argument, but they do not themselves prove it.
