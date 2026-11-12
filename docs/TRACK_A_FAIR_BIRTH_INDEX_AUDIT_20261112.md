# Track A — fair birth-index exactness: adversarial audit, 12 November 2026

This is a role-separated adversarial review, not external human refereeing.

1. **Existence and finiteness:** The countable recursion chooses a whole finite intrinsic component at each step. The previous Lean proof supplies a unique birth stage for every x; finite Q_n membership, rather than an arbitrary least stage, bounds the result by n.
2. **Off-by-one:** The stage indexed n is Q_(n+1)\\Q_n. Therefore x∈Q_n iff birth(x)<n; using ≤ would incorrectly put newly born vertices into Q_n.
3. **Class equality:** Two vertices have equal birth indices exactly when their *complete* unary values agree. Forward implication uses complete-value equality on each new block; reverse implication uses exact new-block equality from merged PR #417.
4. **Strict dependencies:** Every member y of C(x) with C(y)≠C(x) lies in the strict lower part of x, hence was present before x's component was born. There is no false strict comparison among vertices of one component.
5. **Finite index:** On the literal subtype of Q_n, the birth index is a genuine Fin n-valued function. No external numbering or canonical representative inside a component is assumed.
6. **Independent finite falsification:** All 389 reflexive/transitive unary operations on domains of 1–4 elements: 1,345 chosen components, 5,958 pairwise class equalities, 1,250 strict dependency comparisons, 6,803 prefix-membership checks. Independent script is run in CI; it is not a substitute for an infinite Lean proof.
7. **Formal trust and scope:** Exact-head dedicated Lean, #print axioms with standard axioms only, placeholder scan, and full integration are required before merge. These results construct the birth chronology and its dependencies; proving that this chronology has the identical full graph-defined canonical values to an existing finite presentation is still a distinct theorem. No TeX validation markers are promoted.

**Next:** Fix an arbitrary canonical finite index κ on the literal closed fair prefix Q_n whose canonical full unary values agree with C. Compare κ with the new birth index using full-value equality; prove preservation of all strict cross-component dependencies; apply merged `canonicalValue_eq_of_lower_respecting_order`. This is the key missing finite-to-countable bridge.
