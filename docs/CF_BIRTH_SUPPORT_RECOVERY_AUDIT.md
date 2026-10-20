# Adversarial audit: intrinsic recovery of a named C_F birth support

20 October 2026

**Claim:** The literal old support P of a birth-level request r is globally strictly d-closed in the countable birth graph and equals the least globally d-closed hull of its actual old vertices adjacent to the fresh tagged block B.

1. **Class-free strictness referee.** TaggedSupport_dClosed_full gives P ≤d U_{n+1}; the stage image is globally ≤d in the countable graph. Strict d-transitivity gives P globally ≤d, without assuming growth-class amalgamation again.
2. **Label referee.** The finite exact-support certificate is on the *same literal request* r and is transported via the canonical birth embedding. No isomorphic proxy, arbitrary renaming, or quotient is introduced.
3. **Inducedness referee.** oldNeighbourSet_image and dClosedHull_image require the full adjacency iff of the embedded stage, ensuring that no nonedge is silently turned into an edge.
4. **Two-hull referee.** The finite hull is computed inside P; to identify it with the global H of N, use P's global strict closure and finite-cut restriction of H(N) to P. Neither direction follows from finite local minimality alone.
5. **Generator referee.** The exact old neighbours N are taken among vertices of P, not the entire earlier stage or the arbitrary other vertices of C(v). Proving equality with *all* old neighbours inside C(v) requires a separate no-cross and birth-level lemma.
6. **Partial-function referee.** N need not consist of first vertices, so the use of global hull is in the auxiliary mathematical proof and does not enlarge H's declared language domain.
7. **Minimal assumptions referee.** No strong/d-closed genericity, Ramsey property, enumeration homogeneity, or external growth inverse is required beyond the constructed strict finite stages.
8. **Embedded equivalence referee.** This proves the support formula's local kernel. Preservation of complete b-values by every (R,H)-embedding and reflection of the H-domain is a separate theorem.
9. **Lean referee.** The result must pass a full integrated Lean build, explicit #print axioms, no-placeholder and regression checks before any green manuscript marker.

These are independent hostile review angles, not external referee agents.
