# Track B: finite R/H embeddings are intrinsic-level lifts

14 November 2026. Stacked on PR #537, which bridges finite
R/H-substructure closure to the complete auxiliary b-language.
This is a recognition statement about *arbitrary* finite
functional embeddings, not another existence construction.

## Mathematical argument

Let s be a finite R/H-substructure of the actual countable
C_F birth presentation, and e:s→M an arbitrary finite
embedding of the ordered R/H-language. Reflection of the
birth-level preorder determines a strictly increasing
function on precisely the birth levels represented by s:
`finiteEmbeddingLevelMap`. The established finite unique
lifting theorem identifies e with the constructed finite
prescribed lift for those target birth levels, irrespective
of the finite stage cover used in that construction.

The point of this endpoint is its precise quantification:
`e` is NOT assumed to arise from a selected-cut recursion,
nor from any total embedding on an earlier source stage.

## Adversarial checks (six role-separated internal referees)

1. **Intrinsic level referee:** The map is read from e.
   Reflection of the level preorder is used to show independence
   from the representative and strictness on distinct represented
   levels. It is not assumed globally increasing on ℕ.
2. **Source language referee:** s is closed under R and every
   defined H-value. The closure-to-b translation is the exact
   checked source lemma from PR #537, not an assumption that
   all finite graph-induced subsets are substructures.
3. **Ordered rigidity referee:** An embedding preserves edges
   and nonedges, level preorder and the canonical strict order.
   Canonical order is essential to determine the ordinal position
   within a non-singleton fresh block.
4. **Partial H referee:** `FiniteSourceRHValues` requires
   transport of R-values, all defined H-values, and reflection
   of the domain of the partial operation H. The arbitrary
   identity extension outside s is used for evaluation only.
5. **Stage and edge referee:** Any finite stage covering s can
   be chosen for the canonical lift; no whole-stage source map
   is assumed. Empty sources and nonconsecutive source and
   target levels remain valid.
6. **Axiom/scope referee:** The proof invokes the already
   verified finite ExistsUnique theorem twice (for e and
   the constructed lift), not an unproved rigidity assumption.
   It does not assert the countable embedding monoid, an
   infinite-dimensional Ramsey-space axiom, or a rational-level
   lifting theorem. Both new endpoints are printed by exact
   #print axioms checks; the full Lean and placeholder audits
   must pass at the PR head.

These are six independent *mathematical challenge roles* in
one internal review, not reports from external human referees.

## Commands

```sh
lake build BigHrushovski.CFFiniteRHIntrinsicLevelClassification
lake env lean CheckAxiomsCFTrackBFiniteRHIntrinsic.lean
python3 scripts/check_no_placeholders.py
```

Keep this PR as a draft until its prerequisite #537 and this
exact-head stack have passed CI. Avoid promoting manuscript
markers from an unmerged draft. The countable glue is a
separate Track E theorem.
