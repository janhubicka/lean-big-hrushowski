# Track B: fresh-size rigidity under arbitrary finite embeddings

12 November 2026. Stacked on the literal birth coordinates of PR #436.
This patch does not invoke the constructed prescribed finite lift.

## Mathematical content

For a finite b-closed source s, an injective map e preserving
complete b-values and reflecting/preserving the birth-level preorder
carries every whole source birth block **onto** the target birth block.
The source block lies entirely inside s; restricting to the genuine
finite source subtype loses no vertices. Therefore:

```
r.code.1.val = |B_r| = |e[B_r]| = |B_{e(v)}|
             = (e(v)).2.1.code.1.val.
```

A second theorem recovers the complete restricted b-value from
R/H value/domain preservation and canonical-order, graph and
preorder hypotheses. A third gives the same fresh-size conclusion
directly in the original R/H functional language.

## Six role-separated adversarial referees

**Referee A: finite source closure.** The key equality
`(selectedFiniteSet s B).image Subtype.val = B` is justified
by complete b-closedness of s. Without it, an arbitrary selected
subtype could omit part of a birth block and the cardinality
conclusion would be false.

**Referee B: equality, not inclusion.** Exact images of complete
b-values, coupled with both directions of the level preorder,
recover the *whole* target block. A mere induced graph map or
one-sided inclusion `e[B] ⊆ B'` is insufficient.

**Referee C: injectivity.** The equality
`|e[B]|=|B|` uses an explicit injectivity hypothesis on the
genuine finite map. The ordinal-rigidity theorem may also imply
injectivity in some settings, but it is not silently assumed here.

**Referee D: literal request size.** The two endpoints of the
cardinality chain use the literal birth carrier identities of
PR #436, not counts of isomorphism types or merely roots.
The finite ordinal interval may have more than one vertex.

**Referee E: R/H domain.** The R/H version assumes all defined
H-values together with **reflection of H's domain** and uses
`literalClosedSource_bValues_iff_RHValues_of_canonicalOrder`
on the finite closed source. H is not treated as a total function,
and the identity extension outside s is not asserted to be a
global graph embedding.

**Referee F: remaining uniqueness.** These three theorems
remove the fresh-size hypothesis from the request-tag
uniqueness argument, but not the literal support identification,
induced ordered local code comparison or induction through
represented levels. They do not establish arbitrary finite
uniqueness or the infinite embedding monoid. No manuscript
GREEN marker is promoted.

## Mechanical gate

```sh
lake build BigHrushovski.CFArbitraryFiniteFreshSize
lake env lean CheckAxiomsCFTrackBArbitraryFreshSize.lean
python3 scripts/check_no_placeholders.py
```

Require exact-head CI and the standard axiom/source audit.
Six internal adversarial roles do not constitute external human
refereeing.
