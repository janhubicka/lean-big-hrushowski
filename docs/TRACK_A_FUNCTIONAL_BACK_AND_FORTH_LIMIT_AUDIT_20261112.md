# Track A: complete-function preservation in the functional back-and-forth limit

12 November 2026. Seven critical referee roles applied independently; they do not replace outside peer review.

**Precise theorem.** Suppose a coherent increasing sequence of finite globally strong partial graph isomorphisms p_n between two countable graphs exhausts both carriers, and at every n its source and target finite sets are closed under the respective *complete* unary functions. Assume the same finite equivalence preserves and reflects complete unary membership on its source. Then the existing graph-union bijection e:ℕ≃ℕ also satisfies the exact equality C_N(e(x))=(C_M(x)).image(e) for every x. One obtains an induced graph **and** whole-unary isomorphism using one map.

1. **No independent maps:** The graph bijection is precisely the existing `unionEquiv`; the unary proof cannot choose a second map. Its values at finite stages use the certified `union_at_stage` lemma.
2. **Forward direction:** If z∈C_M(x), choose one finite stage containing x. C-closedness of the finite source puts z in the *same* stage. The finite membership biconditional and coherent union transport e(z)∈C_N(e(x)).
3. **Reverse direction:** If y∈C_N(e(x)), the finite target is C_N-closed, so y belongs to the target at the stage already chosen for x. Pull it back through that stage's finite equivalence, invoke the reverse membership implication, and use `union_at_stage` to identify its global e-value with y. No global surjectivity argument is smuggled in beyond the already certified union equivalence.
4. **Graph reflection:** Full induced graph equality comes independently from `unionEquiv_induced`; the new theorem combines its biconditional with exact full unary equality.
5. **Cofinality:** The finite chain must cover both the source and target countable carriers to produce an actual bijection. Merely covering the source yields an injective embedding, not homogeneity or uniqueness.
6. **Negative controls:** Without closure of finite domains, a finite partial map can preserve the restriction of a unary relation on its domain yet omit an entire true unary value outside it. Test such a nonclosed domain explicitly. Finite permutation tests verify actual whole-value equality and graph/nonedge reflection across nested closed prefixes.
7. **Trust and scope:** Exact-head Lean, axioms and placeholder scan, and full repository CI must pass. This is only the **limit theorem**, conditional on having complete-unary closed joint finite steps. Constructing those steps from the all-closed-base extension theorem (draft #455) and deriving homogeneity of the actual functional limit remain separate Lean obligations. Do not change manuscript validation markers.

This design reuses the validated countable graph back-and-forth proof and avoids reimplementing its finite chain, union, injection, surjection or induced graph results.
