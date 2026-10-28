# Adversarial audit: order coherence and literal tag uniqueness for C_F

28 October 2026

## Mathematical input to finite unique level lifting

The newly constructed canonical stage order is recursively defined,
but a finite lifting proof must use its exact successor decomposition.
We prove:

1. The old inclusion `Sum.inl : U_n → U_(n+1)` preserves and
   reflects strict order, with no renumbering.
2. Every old vertex precedes every freshly introduced vertex.
3. Between fresh vertices the order is exactly lexicographic in
   the canonical numerical request ranks and then in the natural
   finite ordinal.
4. Strict comparison of complete literal request keys implies strict
   order of all corresponding fresh vertices.
5. The complete request key plus the fresh ordinal determines one
   literal tagged fresh vertex, not only an isomorphism type.

## Separate hostile perspectives

- **Predimension/data:** The new results make no assertion about
  class membership or a d-closed extension property. Those are supplied
  by previously verified finite-stage modules.
- **Ordering:** They use *the recursively inherited stage order*.
  An arbitrary rank or independently chosen linear order would not
  prove the manuscript's finite-lifting claim.
- **Dependent types:** Equal literal request keys are converted to
  equality of the full dependent request records *before* comparing
  their fresh `Fin` ordinals. Equality of ordinals across unrelated
  finite carriers is insufficient.
- **Empty/new level:** All statements about a fresh vertex are
  conditional on its existence. Empty request catalogues cause no
  false existence claims.
- **No circularity:** The new level's order is built from old-stage
  ranks and the finite ordinal, and proof of coherence does not
  assume uniqueness of level lifting.
- **Uniqueness boundary:** These statements do not show that a
  prescribed finite source can be transported to a target request.
  They do show its target *must be unique once the complete transported
  support, graph code and ordinal are fixed*.
- **Verification:** Build of the whole imported Lean tree, exact axiom
  endpoints, and placeholder audit are required for certification.

These checks are adversarial roles carried out in the project, not
human referee reports.
