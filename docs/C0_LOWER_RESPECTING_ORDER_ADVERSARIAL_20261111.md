# Track A: lower-respecting chronological reordering — adversarial review

11 November 2026. Seven internal adversarial referee roles. These are not external peer reports.

## Proposed lemma

For a finite graph and two component indices κ and κ', assume the indices partition vertices into *exactly* the same whole components. Also assume: whenever v belongs to the complete old canonical value of u and lies in a different component, the index of v is strictly earlier in κ' than that of u. Then **all complete canonical values agree** between κ and κ'. No relation is required between incomparable components.

## Referee roles

1. **Hypotheses:** Retaining the component partition is necessary; merely keeping component cardinalities would be insufficient. Empty chronological levels are allowed.
2. **Strict dependency:** The assumption excludes same-component pairs; an entire component is allowed to have multiple vertices and should never force strict order within itself.
3. **Graph-edge orientation:** For a cross-component edge u-v with κ(v)<κ(u), v is a one-step predecessor of u and hence belongs to the complete value of u. The new strict-lower condition gives κ'(v)<κ'(u).
4. **Reverse direction:** If κ'(v)<κ'(u), the old indices cannot be equal by partition preservation. If κ(u)<κ(v), applying the same argument to the reverse edge v-u gives κ'(u)<κ'(v), a contradiction. Graph symmetry is indispensable.
5. **Full unary:** Invoke the existing certified `canonicalValue_eq_of_same_components_and_edge_orientation`, whose conclusion is equality of the *entire reachability closure*, not equality of direct back edges or a cardinality.
6. **Falsification:** Exhaustively enumerate all simple graphs of up to four labelled vertices and component-index maps with all possible permutations of occupied component levels. For every new order satisfying strict-dependency precedence, compare complete canonical values; include a reversed-edge negative control.
7. **Trust and scope:** Exact-head Lean kernel, axiom, placeholder and finite-regression gates remain mandatory; do not promote manuscript GREEN markers until they pass. This lemma is a **conditional finite criterion**. It does not construct a global fair birth-index function or prove the selected uniform internal ordering, or the countable functional Fraïssé homogeneity conclusion.

## Intended use

Combine the certified fair-prefix and birth-stage theorems with the finite canonical closed-heredity presentation. Prove the new birth-based finite index has the same intrinsic complete-unary equality classes as the old index, and every strict lower component precedes its generator. The lemma then gives exact equality of full values. This abstracts and shortens the edge-orientation comparison previously planned separately.
