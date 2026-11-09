# Track A: enabled-component existence — adversarial validation

9 November 2026. This is a panel of *internal* mathematical referee roles, not independent human referee reports.

## Claims

For every finite Q⊆ℕ and every finite-valued reflexive/transitive unary closure C on ℕ, there exists x∉Q with L(x)=C(x)\P(x)⊆Q. Among all such x, there is a least numerical x. Under exact cofinal finite canonical C₀ stages and C-closedness of Q, one obtains a genuine minimal strong step Q < Q∪P(x) and a globally strong new prefix.

The first existence theorem does **not** require Q to be C-closed. It uses finiteness of Q, infinity of the carrier, and strict cardinal descent of complete C-values. The graph conclusions depend on the actual canonical finite stages.

## Referee 1 — the carrier must be infinite

The least outside vertex is not available for an arbitrary finite carrier: if Q is the whole carrier, no further component exists. The theorem is intentionally stated over ℕ. The proof gives an explicit unlisted label above the supremum of the finite set Q. No artificial "infinitely many components" assumption is used.

## Referee 2 — rank minimization is local to the unlisted set

Choose x outside Q minimizing the natural number |C(x)|, which exists by well-ordering of ℕ and finiteness of each C(x). If y∈L(x) and y∉Q, the already merged strict-lower lemma gives |C(y)|<|C(x)|, a contradiction. This does not require globally sorting all components by closure size. Such a global sorting is incorrect when infinitely many low-rank components exist.

## Referee 3 — strict lower, not same-component vertices

For y∈P(x), the complete unary values and ranks are **equal**. The cardinal descent lemma applies only to y∈L(x)=C(x)\P(x). The theorem therefore adds a *whole* intrinsic component at one step and does not erroneously put a classmate into the lower part.

## Referee 4 — priority versus rank

The first minimization of |C(x)| proves nonemptiness of the set of eligible vertices. A **second**, independent minimum of the numerical labels among eligible vertices gives the fair priority choice. Choosing the least closure rank *at every future step* would not be a fair algorithm in the presence of infinitely many rank-one components. The theorem does not conflate the two minima.

## Referee 5 — graph conclusion has its stated hypotheses

A complete unary closure by itself says nothing about graph predimension. The countable graph step invokes the previously verified canonical finite-stage interval theorem via the enabled-component step. It also keeps Q closed, so x∉Q forces P(x)∩Q=∅. The new set is globally strong because of the separate finite-closed-set global-strong theorem.

## Referee 6 — scope and remaining fairness proof

The existence of an eligible least-priority choice at *one* finite stage does not prove the complete infinite recursion or eventual selection of every component. These still need:
- a definition of the recursive finite prefixes Q_n with exact closure preservation;
- a proof that the numerical minimum eligible class is removed at each step;
- induction on |C(x)| and finite lower dependencies to show every class appears after finitely many steps;
- construction of a vertex enumeration of order type ω and agreement with the full unary values.

No countable enumerating order or GREEN manuscript marker is asserted here.

## Referee 7 — Lean trust

The new module is BigHrushovski/C0EnabledComponentExistence.lean; three exact theorem endpoints are audited through CheckC0EnabledComponentExistence.lean, plus a placeholder scan, the finite one-component exhaustive check, and a second independent complete-unary enabledness regression in a dedicated GitHub Actions workflow.

The second regression independently exhausts all 389 reflexive/transitive unary operations on nonempty carriers of size at most four, 5,541 proper finite subsets, and 7,899 eligible vertices. On 2,093 closed proper subsets, the least eligible numerical vertex always yields a strictly larger closed union with its entire component. This is a finite falsification test, not a proof of the infinite-carrier theorem. CI is pending at creation. No sorry/admit/axiom is introduced, and ordinary umbrella Lean CI alone would not build this separately imported module.
