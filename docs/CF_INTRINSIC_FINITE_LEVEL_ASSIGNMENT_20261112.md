# Track B: intrinsic target-level assignment from arbitrary finite embeddings

12 November 2026. This result is independent of the auxiliary b-values,
canonical order, graph adjacency, and R/H function values. It extracts
exactly the data required as input to the merged prescribed finite
existence construction.

## Mathematical argument

Let s be any finite set of birth-labelled vertices, and
e:s→M_F^† preserve and reflect the weak preorder of birth levels.
For every represented source level i, all its vertices have images
at the same target level: each pair satisfies the preorder in
both directions, and thus its images do as well. Denote that
target level by h(i). If i<j are represented, their target
levels satisfy h(i)<h(j), since the reverse inequality would
reflect j≤i, a contradiction. Hence h is strictly increasing
on the represented levels.

The map h is forced there, but no assertion can be made about
unrepresented source levels. The Lean definition sets h(i)=0
outside the represented set as an arbitrary convention, **not**
as a claim of a globally strictly increasing map.

## Six adversarial referee roles

**Referee A (level equality).** Both directions of the weak
birth-level preorder are used to infer equality of target birth
levels for source vertices on the same represented level.
Preservation in one direction alone does not justify this.

**Referee B (strict increase).** The proof needs both the forward
order and its reflection. To show target h(i)<h(j) for i<j,
assuming h(j)≤h(i) would imply j≤i; this directly contradicts
the strict source comparison.

**Referee C (representatives).** Choice of one vertex at level i
is harmless only after proving image-level independence.
No choice of a global embedding or a linear enumeration of s
is assumed.

**Referee D (empty source and gaps).** If s is empty, the
assignment is identically zero and strictness on the empty set
is vacuous. If s has no vertices at level 0, or any gap in
the source stages, there is no obligation on the unused values
of h. Target level 0 is allowed for the first represented level.

**Referee E (uniqueness scope).** Any alternative level assignment
satisfying exact target labels agrees with h **on represented
levels**. Claiming equality of functions on all ℕ would be
false, because unused source levels may be assigned anything.

**Referee F (connection to the remaining proof).** The existence
theorem `finiteSourcePrescribedLift_exists_ordered` accepts
`StrictOnRepresented`. This lemma establishes that every
arbitrary finite embedding preserving the level preorder has
an eligible h. This does not prove it coincides with the
constructed lift; the complete local request-tag comparison
and induction remain missing.

## Exact verification gate

```sh
lake build BigHrushovski.CFIntrinsicFiniteLevelAssignment
lake env lean CheckAxiomsCFTrackBIntrinsicLevelAssignment.lean
python3 scripts/check_no_placeholders.py
```

All exact endpoints must have standard axioms in the umbrella
audit. Keep draft until its exact-head CI is green.
The six internal referee roles are not external human referees.
