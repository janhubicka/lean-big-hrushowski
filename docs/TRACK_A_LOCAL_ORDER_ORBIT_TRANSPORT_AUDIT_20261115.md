# Track A — finite local-order orbit transport: seven adversarial checks

15 November 2026. These are separate internal mathematical criticisms, **not** reviews by outside human referees.

**Claim to certify.** Let \(e_1,e_2:A\to R\) be two induced *complete-functional isomorphisms* of the same finite one-generated closure onto a selected representative. Their change of coordinates \(g=e_2^{-1}\circ e_1\) is a complete-functional automorphism of \(A\). If the two identifications agree on a lower part \(P\), then \(g\) fixes \(P\) pointwise and aligns the two transported local orders. If an automorphism preserves an injective numeric rank for every vertex, it is the identity. This proves the finite transport and free stabilizer assertions without selecting a global family of local types.

**Referee 1 — correct composition.** The order of composition matters: \(g=e_2^{-1}\circ e_1\), not \(e_1^{-1}\circ e_2\). The proof records the exact identity \(e_2(gx)=e_1(x)\). Both graph and unary identities are derived from that equality.

**Referee 2 — fixed old vertices.** The hypothesis \(e_1|_P=e_2|_P\) gives \(g(x)=x\) for each \(x\in P\). This is a *pointwise* assertion, essential to extension over a named closed base, not merely preservation of \(P\) as a set.

**Referee 3 — induced graphs.** The graph conclusion is a biconditional. A forward-edge-only morphism would be insufficient to obtain an automorphism or to align the later induced Ramsey copies.

**Referee 4 — full unary values.** The proof uses exact equality
\[
 C_R(e_i x)=e_i[C_A(x)]
\]
and the injectivity of the finite set image under \(e_2\) to deduce
\(C_A(gx)=g[C_A(x)]\). Merely preserving immediate old neighbours or closure inclusions would not establish this.

**Referee 5 — orders and group freeness.** Numeric rank on a finite ordered representative is injective. An automorphism fixing rank at every vertex must be the identity; this gives a free action on local orders, not a pointwise automorphism-invariant preferred order. The local orbit may contain several labelled orders.

**Referee 6 — explicit falsifier.** In the finite canonical presentation
\[
 \varnothing\subset\{a\}\subset K_4,
\]
the last increment \(B=K_4\setminus\{a\}\) is minimal strong: the predimension is 2 at the two endpoints and 3 at each intermediate \(P\cup S\), \(\varnothing\ne S\subsetneq B\). The lower-part stabilizer is \(S_3\), and its orbit on local orders has six members. A *pointwise invariant order* is impossible. The independent finite test enumerates all 36 pairs of the six functional automorphisms and checks both adjacency and **full** unary values.

**Referee 7 — verification boundary.** The PR creates only a finite **transport** interface and a free local-order stabilizer. It does not yet construct a global choice of local representative orbits along the fair component chronology, nor does it prove tail extension, recurrence or the ordered Ramsey theorem. Require the exact-head Lean build, six named axiom reports, no placeholders, independent finite regression and whole-repository Lean CI before merging. No manuscript TeX or validation markers are changed in this Lean PR; the separate manuscript clarification is draft PR #179 in the paper repository.
