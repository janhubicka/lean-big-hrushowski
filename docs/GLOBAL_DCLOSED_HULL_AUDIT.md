# Adversarial audit: least global d-closed hull under strict exhaustion

19 October 2026

## Claim and proof

For any submodular finite predimension d on an arbitrary ambient vertex type, and any covering `DClosedChain d` of finite strictly d-closed stages, every finite set S has a least **finite globally strictly d-closed** hull H(S).

Choose a finite stage U_n containing S. The finite `dClosedHull S U_n` is d-closed in U_n, and U_n is globally d-closed, so H is globally d-closed. For any competing globally d-closed T containing S, strict finite-cut restriction gives `T∩U_n ≤d U_n`. Minimality of the finite hull inside U_n now yields `H⊆T∩U_n⊆T`.

The argument proves independence of the finite containing stage and yields the usual closure laws: extensivity, monotonicity, idempotence. The resulting `birthDClosedHull F K` is a concrete global operation on finite sets of actual C_F birth-labelled vertices. Its restriction to sets of block roots supplies the graph-theoretic H of the manuscript.

## Eight hostile mathematical checks

1. **Strictness:** The global hull is strictly d-closed, not merely self-sufficient. Both finite hull construction and stage chain use `IsDClosed` rather than weak `IsStrong`.
2. **Finite character:** Only finite-stage hulls and comparisons of finite sets occur. No infinite predimension `δ(X)` is invented.
3. **Container independence:** A finite hull computed inside one stage is not automatically least against arbitrary globally closed sets T. Intersecting T with the chosen stage and applying the *finite-cut restriction lemma* closes this gap explicitly.
4. **No free-amalgamation shortcut:** No growth-class free-amalgamation theorem, uniform inverse bound, or homogeneity assumption is needed to define the global hull once the actual strict chain exists.
5. **Correct ambient:** `DClosedChain` requires finite stages covering every vertex and strictly d-closed successor steps. An arbitrary sequence of strong but non-strict stages would be insufficient.
6. **Invariance and functions:** Closure equality in a chosen stage is exact because both sets are least globally d-closed; it is not just an embedding-image inclusion. This avoids noncanonical choices when defining H.
7. **C_F instance:** The birth graph, finite stage images and global strict chain are already kernel-certified. The new specialization introduces no second quotient, arbitrary vertex enumeration or renaming.
8. **Remaining boundary:** Having H on finite vertex sets still does **not** prove H(R(v))=C(v), recover complete blocks from (R,H), or prove equivalence of functional embeddings. Those require actual root reachability and the rooted-block induction.

These are role-separated internal mathematical audits, not independent outside referees. No theorem is GREEN until integrated Lean build, exact axiom and no-placeholder checks pass.
