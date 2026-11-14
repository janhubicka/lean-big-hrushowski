# Track A: exact finite functional-image closure — seven adversarial checks

12 November 2026. Seven distinct internal critical reviewer roles, not external human peer review.

**Claim.** An injective finite complete-functional embedding f:U→N satisfies C_N(f(u))=f[D(u)] for each u. Hence f[U] is C_N-closed, unary-membership tests are reflected exactly, and induced adjacency on its literal subtype agrees with U if the map is induced. If N has cofinal canonical C₀ stages, this finite closed image is globally strong automatically.

1. **Complete values/referee:** Equality C_N(f(u))=f[D(u)] is essential, not mere inclusion of D(u) or preservation of direct old neighbours. Otherwise new dependencies outside the image can violate closedness.
2. **No hidden injectivity/referee:** Image *closedness* itself does not require injectivity, since every element of C_N(f(u)) is an image by equality. Reflection of membership does require injectivity; the hypotheses are deliberately different.
3. **Unary reflection/referee:** If f(y)∈f[D(x)], an injection lets us cancel f from the witness and recover y∈D(x). The result concerns complete membership, not a cardinality comparison.
4. **Graph/referee:** The induced graph theorem is a biconditional: absence of an edge in U is also absence in the image graph. It is not deduced from unary equality, but from the explicitly supplied induced graph embedding.
5. **Global strongness/referee:** In the countable C₀ graph, every finite C-closed subset is globally strong by the separately certified canonical-stage theorem; do not infer strongness from arbitrary functional data in an arbitrary graph. Both hCover and hStage remain explicit.
6. **Negative-control/referee:** A finite unary image can preserve only restricted membership while its full target C-value contains an outside vertex, making the image nonclosed. The finite regression must include a concrete example and all injective relabellings of small complete unary systems.
7. **Trust/scope/referee:** Four exact `#print axioms` endpoints, a dedicated Lean build, the standard axiom/placeholder audit, full repo integration and independent finite checks are required. This is a reusable finite-image lemma, not a proof of the finite joint extension step or the canonical ordered expansion; keep those manuscript assertions unpromoted.

**Use in the next proof.** Apply this to the output of the actual all-closed-base extension theorem (#459) with U being the chosen finite canonical source extension. Its image is automatically C-closed, and then globally strong. It is the prospective target domain of the next closed functional partial isomorphism.
