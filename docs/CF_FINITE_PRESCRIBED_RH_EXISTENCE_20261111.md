# Track B: finite prescribed lifts in the full (R,H) language

11 November 2026. This candidate is stacked above #411 and #415.
No manuscript validation marker is changed pending kernel verification.

## Mathematical statement

Let s be a finite b-closed subset of the actual C_F birth-labelled
generic, and let level assign strictly increasing target levels on
only the represented birth levels of s. The existing finite lift
g:s→M is now shown to preserve and reflect the exact canonical
birth order and birth-level preorder, and to transport whole
b(v)-values onto b(gv). The already established equivalence of
closed-source embeddings then gives:

- exact image of R(v) for every v∈s;
- exact image of H(T) for every finite T⊆s of birth roots;
- preservation AND reflection of the domain of partial H, for
  every finite subset T⊆s.

The auxiliary total map in the Lean statement is the function
equal to g on s and the identity outside s. It is only a
**notation for evaluating ambient finite-set images**. Its
value elsewhere is never required to preserve edges, order or
functions. The genuine embedding remains the subtype map g.

## Independent adversarial roles

**Referee 1 (the finite source).** `IsBirthBlockClosed` for a
Finset entails `IsBirthBlockClosedSet` on the associated membership
predicate. This is an equality of predicates, not an assumption
of extra unlisted closure or a source containing all ambient stages.

**Referee 2 (complete b-values).** The proof uses
`finiteSourceBirthBValue_image`, which requires finite
b-closedness. A restricted b(v) that omits target support
vertices would NOT suffice to apply the value equivalence.
It is vital that the image of each restricted source value
recovers the entire literal ambient b(v).

**Referee 3 (partial-map extension).** Applying an extension
outside s would be illicit if inducedness or injectivity were
ever required globally. The source-local equivalence theorem
has hypotheses only on X and was expressly written to handle
such partial maps. Its external identity extension is harmless.

**Referee 4 (order).** The exact canonical order is essential
for selecting first vertices and reflection of the domain of H.
Mere preservation of birth levels, unordered blocks, or graph
edges alone would not imply the domain statement.

**Referee 5 (empty and initial cuts).** The source may be empty.
The finite source can meet a level n without containing a vertex
at any earlier stage, so no global strictly increasing extension
of the prescribed level map is permitted or needed.

**Referee 6 (scope and completeness).** This proves only
existence of finite maps with complete R/H properties; it does
not compare arbitrary embeddings with the canonical lift.
The remaining finite uniqueness induction must derive equality
of local request tags (full named support, fresh size, ordered
adjacency matrix) and equality of finite ordinal positions
from an arbitrary functional embedding. Infinite embeddings
and monoid identification are further separate tasks.

## Exact-head verification gate

```sh
lake build BigHrushovski.CFPrescribedFiniteRHLift
lake env lean CheckAxiomsCFTrackBRHExistence.lean
python3 scripts/check_no_placeholders.py
```

The umbrella workflow also checks the whole project's Lean
imports and functional regressions. This note is a mathematical
adversarial audit, not a substitute for exact-head kernel CI.
