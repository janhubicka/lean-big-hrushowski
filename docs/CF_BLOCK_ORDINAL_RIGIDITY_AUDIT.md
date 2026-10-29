# Complete ordered C_F blocks preserve all ordinals

28 October 2026

## Claim and proof

`birthOrdinal_image_on_closedSet_of_canonicalOrder` proves that a
map preserving complete b-values, the level preorder and the
canonical order on a b-closed source preserves every internal
ordinal of every source block. The source can be empty or infinite.
The map is unrestricted outside the source.

The proof first derives the whole block-image equation using the
existing complete-value and level-preorder theorem. It then obtains
an increasing surjection between the two finite ordinal intervals.
An increasing surjection is an order isomorphism, so Mathlib's
`Fin.coe_orderIso_apply` gives equality of each index. There is no
assumed equality of ordinals in this deduction.

Global injectivity and graph adjacency are unnecessary for this
limited conclusion. Strict increase gives injectivity inside each
block; the exact image equation gives surjectivity.

## Adversarial panel

Three separately spawned internal model referees reviewed the actual
new Lean module: mathematical proof, Lean statement/dependencies,
and counterexamples/scope. All three found no mathematical defect.
The Lean referee also checked the exact Mathlib signatures used by
the finite-order-isomorphism argument. These are internal model
reviews, not external human referee reports.

The panel identified the following essential negative controls:

- Strict increase without surjectivity permits Fin 1 -> Fin 2,
  mapping 0 to 1.
- Surjectivity without order preservation permits the transposition
  of Fin 2.
- Nonstrict monotonicity with surjectivity permits Fin 3 -> Fin 2,
  mapping (0,1,2) to (0,0,1).

The hypotheses exclude all three. Empty source sets require no
fictitious vertex; individual request blocks are nonempty by the
existing minimal-extension certificate.

## Validation and remaining scope

Five exact theorem endpoints are registered in `CheckAxioms.lean`.
Kernel acceptance, the axiom audit, the placeholder scan and the
existing regressions are checked by the repository's complete CI.
The CI result must be successful before marking the manuscript's
ordinal-preservation statement as Lean-verified.

This result supplies the ordinal part of uniqueness. Transporting
the actual named requests and their full ordered graph codes,
assembling all blocks at a level, and induction through represented
levels remain necessary for finite lifting. It does not prove the
embedding-monoid theorem. For unrestricted formal parameters,
K = 0 gives an empty tower, so that later theorem must establish
nonempty levels under the manuscript's hypotheses.
