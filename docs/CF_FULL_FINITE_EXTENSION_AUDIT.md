# Adversarial review: complete finite C_F extension (17 October 2026)

**Exact statement:** for any finite ordered graph G with `IsGrowthSparse F univ`, finite sets `a ≤d b`, and a *given* induced embedding of the literal subtype of a into the countable tagged birth graph whose image is globally strictly d-closed, there is an induced embedding of the literal subtype of b into that graph, fixing every original vertex of a and with globally strictly d-closed image.

The only numerical hypothesis is the explicit integer inverse domination `F(m) ≤ 2(k+1) ⇒ m ≤ K(k)`; monotone/unbounded real growth gives this separately. No recurrence, free amalgamation property of the growth class, or big Ramsey statement follows from this theorem alone.

## Independent hostile checking roles (internal audit)

1. **Finite-decomposition referee:** `Predimension.finite_minimal_decomposition_of_dClosed_absolute` decomposes each *strict* d-closed interval, without a global strong-exhaustion assumption. Every intermediate has its literal vertex set and is nested in b.
2. **Growth referee:** The class hypothesis must hold on the **whole finite graph G**, not just the first base a; heredity makes every intermediate s∪(t\s) growth-sparse. Otherwise a minimal interval outside a stated target could fail the growth bound and would not appear in the catalogue.
3. **Inducedness referee:** Local validity includes the iff for adjacency, not only a forward homomorphism. Cross-boundary nonedges are captured by the validated normalized one-step response.
4. **Strictness referee:** The inductive invariant uses global IsGloballyDClosed of the image at every step; strongness would be insufficient, and d-closedness inside a finite stage would not automatically imply global d-closedness without the separately proved global stage closure.
5. **Naming referee:** The map on the split carrier is transported back to the original `{v // v∈t}` using a genuine equivalence. Old vertex values are equal pointwise at every step; this is not extension up to an isomorphic replacement of the prescribed source.
6. **Image referee:** Reindexing with the finite subtype equivalence does not change the image set; equality of images is proved before carrying over global strict d-closedness.
7. **Countability/genericity referee:** A global d-closed finite extension property for the tagged birth graph is **not** alone an identification of its graph reduct with the published M_F. One still needs class membership/free amalgamation under the hypotheses on F, finite d-closed coverage, and uniqueness of the strong Fraïssé limit. Countability, finite induced stages, and global stage closure have separate Lean results.
8. **Lean kernel referee:** Green status requires a full build of this branch plus an exact `#print axioms` check and placeholder scan; older successful workflows for its two inputs do not certify this new assembly.

## Failed-premise controls

- If the old source is merely induced but not globally d-closed, the catalogue response over a closed support does not justify the desired globally d-closed extension.
- If G is growth-sparse only on a but not on b, one cannot infer the required local growth hypothesis for all steps.
- If the old maps agree merely up to isomorphism, the prescribed-embedding extension property does not follow.

No external referee agents were spawned. These are separate internal adversarial proof checks, recorded independently of the Lean kernel run.
