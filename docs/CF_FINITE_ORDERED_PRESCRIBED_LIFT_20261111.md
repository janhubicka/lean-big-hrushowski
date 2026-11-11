# Track B: canonical order of finite prescribed-level lifts (11 November 2026)

This patch is stacked on the finite birth-preorder and whole-block
image bridge of PR #411. It establishes the canonical manuscript
order for **the same** constructed finite \(\mathcal C_F\) lift,
not a new independently chosen witness.

## Adversarial referee panel (internal, six roles)

1. **Finite versus countable order.** The proof imports the proved
   `stageLt_iff_canonicalBirthLt` of
   `CFStageBirthOrderCoherence.lean`. An arbitrary finite order
   would not suffice. The recursive `stageLinearOrder` is used
   at *both* source and target stages.

2. **Partial-source discipline.** `VerifiedCutMap.strictMono` is
   defined on `SupportCarrier ... (stageCut ...)`, not the entire
   source stage. We use only this selected subtype and its canonical
   literal equivalence with the original finite set. No unproved
   extension to the whole stage is smuggled in.

3. **Reflection as well as preservation.** Strict monotonicity of
   a function on a linearly ordered subtype reflects `<`, by
   trichotomy and asymmetry. This is proved explicitly rather
   than assuming a surjection or a global order automorphism.

4. **Gaps and level zero.** The source cut at a sufficiently
   late stage contains exactly the original source vertices,
   while the target map is into the automatically calculated
   target stage. The code does not require the prescribed map
   to extend to a strictly increasing function on every
   intermediate natural-number source level.

5. **Same concrete map.** The complete ordered existence theorem
   uses the very same `finiteSourcePrescribedLift` for graph,
   complete b-values, target birth labels, full level preorder
   and canonical strict order. It cannot be inferred by
   combining unrelated existential witnesses.

6. **Scope and verification.** Even with all these conditions
   proved, uniqueness among arbitrary embeddings, the precise
   partial R/H function values, and infinite embedding-monoid
   identification are separate. The four-value comparison for
   the finite R/H language should now be obtained by applying
   `literalClosedSource_bValues_iff_RHValues_of_canonicalOrder`
   after converting finite b-closedness to the closed-set
   predicate. No manuscript GREEN marker can follow without
   kernel verification of the exact theorem and the published
   finite lemma's remaining uniqueness clause.

## Mechanical gate

```sh
lake build BigHrushovski.CFPrescribedFiniteOrderedLift
lake env lean CheckAxiomsCFTrackBOrderedExistence.lean
python3 scripts/check_no_placeholders.py
```

The umbrella Lean workflow discovers the added axiom module.
Run exact-head CI and check the kernel; the English audit alone
is not Lean certification.
