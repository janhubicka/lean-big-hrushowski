# Track A: fair vertex-order interface — seven adversarial referee roles

12 November 2026. Internal proof audit only; no claim of external human refereeing.

The proposed relation orders vertices first by their intrinsic fair component birth stage, then by arbitrary numerical local keys which are injective **on each component**. The theorem verifies asymmetry/irreflexivity, transitivity, strict totality, convex components, initial fair prefixes, an exact finite predecessor set and absence of a greatest vertex.

1. **Local-key/referee:** Local keys need not distinguish vertices in *different* components: those are already separated by their birth stages. But within one component equality of local keys must imply equality of vertices. This is the only additional assumption for strict totality.
2. **Convexity/referee:** A vertex between two members of one class must have the same birth stage. The claim is about *birth components*, not about an arbitrary unary closed set C(x), whose lower part is a union of earlier components.
3. **Initial segment/referee:** Because x<y in the proposed order implies birth(x)≤birth(y), an old Q_n cannot contain y but omit x. Note that arbitrary **partial** components cannot be prefixes at this scale.
4. **Order type/referee:** Finite predecessor sets and no greatest vertex are established on the countably infinite carrier ℕ; finite simulations cannot test absence of a greatest vertex and must not be cited for that part. Together with strict totality, these properties characterize an order of type ω. This module does not manufacture an explicit order isomorphism ℕ≃oℕ.
5. **Functional/referee:** Chronological ordering of *components* does not depend on local keys. Hence the full unary-value theorem from merged #427 remains valid for every such internal ordering; nothing here is a new finite graph-value proof.
6. **Manuscript/referee:** Taking numerical vertex labels as keys gives a valid order of type ω but generally **fails** the uniform chosen representative convention used for the paper's Ramsey expansion. It must not be promoted to the manuscript's final ordered-language theorem.
7. **Formal trust/referee:** Nine exact theorem endpoints require dedicated exact-head Lean kernel build, standard axiom audit, placeholder scan and independent exhaustive finite regressions; run full repository CI separately before any merge. No manuscript GREEN markers are changed.

The generic local-key assumption is designed to accept the eventual uniform local order choices of Track D without repeating the global type-ω argument. Its future use must still verify coherence of those local choices under closed embeddings.
