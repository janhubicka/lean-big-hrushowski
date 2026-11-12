# Track F — global SCC order signature (12 November 2026)

Stacked on Track F canonical local fibres PR #413, itself stacked on
the orientation integration PR #270. **No manuscript or validation marker
changes.**

## Kernel proof endpoints, pending exact-head CI

New module `BigHrushovski/N0GlobalComponentSignature.lean`:

1. `successorFirst_lowerPart_before_component`: in every *actual*
   successor-first enumeration, not only in a constructed lexicographic
   order, every element of the strict successor part
   `P_B=C_B\setminus B` precedes every element of `B`.
2. `successorFirst_lowerPart_initial_in_closure`: the lower part is
   an initial segment in the **induced order on C_B**, even if unrelated
   SCCs outside `C_B` appear earlier in the global order.
3. `globalComponentOrderSignature`: an actual labelled enumeration
   yields its SCC ranking and all intra-SCC pairwise comparisons.
4. `enumeration_eq_of_same_globalComponentOrderSignature`: two
   component-interval enumerations with the same signature are literally
   equal; there is no quotient by isomorphism or automorphism.
5. `enumeration_eq_of_same_ranking_and_closure_orders`: component
   ranking together with the inherited strict orders on the actual
   one-component closures `C_B` uniquely determines the global
   component-interval enumeration.
6. `componentIntervalOrderSignature_card` and
   `successorFirstIntervalOrderSignature_card`: mapping to signatures
   preserves the number of labelled enumerations in either family.

The key logical dependence of uniqueness is the previously certified
`enumeration_eq_of_same_component_order_and_local_orders`, which
requires SCCs to be genuine intervals. No claim is made of a surjection
from arbitrary local code-fibre choices to global permitted orders.
The exact product count and the infinite big Ramsey theorem remain open
Lean proof obligations.

## Adversarial referee panel (role-separated internal checks)

1. **Interleaving referee.** A directed triangle plus an isolated
   vertex admits interleaved enumerations `(0,3,1,2)` and
   `(0,1,3,2)` with the same component ranking and intra-SCC
   comparisons. They are distinct. The interval hypothesis is
   essential, and the regression explicitly rejects its omission.
2. **Successor referee.** For an oriented edge `0→1`, the order
   `(0,1)` violates successor-first; it must not be used to infer
   lower-part initiality. The order `(1,0)` satisfies the hypothesis.
3. **Closure referee.** The statement is initiality *inside* the actual
   successor closure `C_B`, not in the whole vertex set. Unrelated
   components can occur at arbitrary earlier positions.
4. **Labelled-order referee.** Equality of signatures implies equality
   of `Fin n ≃ V` enumerations on the fixed labelled carrier.
   A calculation involving only isomorphism classes would not suffice
   for the manuscript's expansion count.
5. **Local-completeness referee.** The signature records all pairwise
   comparisons within each actual SCC. It does not record only arrows,
   and does not assume that SCCs are singletons.
6. **Quantifier referee.** The closure-order uniqueness lemma requires
   agreement of comparisons between all pairs of vertices in each
   `C_B`; there is no hidden assumption that global positions of
   unrelated vertices coincide.
7. **Certification referee.** Six named nontrivial lemmas are included
   in an explicit `#print axioms` audit. Passing Python enumeration is
   neither Lean certification nor independent human peer review.

The Python test independently enumerates all 653 orientations on at most
four vertices, checks 13,730 SCC-interval enumerations have unique
signatures and verifies lower initiality in the 3,714 successor-first
SCC-interval orders. It also checks lower initiality for successor-first
noninterval enumerations. The interleaving and backward-edge negative
controls are mandatory.

## Next mathematical step

Define the restriction of a global vertex enumeration to each induced
closure `C_B` as a bijective enumeration. Prove its lower part is
positionwise fixed when the previous components have their chosen orders,
and show that the local canonical code condition is equivalent to
membership in the already-certified canonical fibre. Then prove the
surjectivity of the component-ranking plus local-choice reconstruction
and use uniform dependent-history fibre counting. No full formula is
marked validated before that step and its Lean certification.
