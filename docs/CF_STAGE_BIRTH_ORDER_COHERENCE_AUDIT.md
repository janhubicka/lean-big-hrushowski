# Adversarial audit: order agreement on C_F finite stage images

28 October 2026

## Claim

The finite stages U_n carry the recursively inherited exact request
order; the actual birth-labelled countable carrier carries the
level/request-rank/ordinal order. The theorem
`stageLt_iff_canonicalBirthLt` identifies them under the **literal**
canonical map `toVertex F K n` for every finite stage and all pairs
of its vertices.

The finite tower therefore has a single coherent order. In particular,
`stageLt_ascend_iff` certifies the exact order under *any number*
of old-stage inclusions, not merely at one successor step.

## Separate hostile checks

1. **Old-old:** The previous stage order is preserved and reflected
   via `stageOrder_old_iff`; the induction hypothesis handles the
   corresponding birth-labelled vertices.
2. **Old-new:** Every old vertex has birth index strictly below the
   new block's index, and the countable birth order first compares
   those levels.
3. **New-old:** Both orders prohibit reversal of the previous case:
   stage asymmetry and nondecrease of birth levels rule it out.
4. **New-new:** Both constructions use the very same canonical
   request rank and fresh ordinal. There is no arbitrary comparison
   of request tags or hidden renumbering.
5. **Empty stages:** Proof is by structural induction on literal
   sum carriers. The empty first stage and potentially empty fresh
   levels require no fictitious vertices.
6. **Iteration:** `toVertex_ascend` ensures that the same birth
   label represents a vertex at every later stage; thus pairwise
   order agreement yields arbitrarily many-stage coherence.
7. **Scope:** This certifies the order in the domain and codomain
   used by finite lifting. It does NOT yet construct a lift for
   a finite closed source or prove the uniqueness of such a lift.
   Additional transport of named local requests and their ordinal
   labels is required.
8. **Kernel:** Only a complete successful build, exact axiom audit
   and placeholder scan permits these statements to be marked
   Lean-verified.

These are adversarial mathematical checks conducted within the
project, not independently contracted human referees.
