# Adversarial audit: C_F growth-class normalized local codes

16 October 2026

## Mathematical content

Let P and B be finite types, with B linearly ordered. Let G be
a graph on P ⊕ B whose P-part agrees with the named old graph,
and suppose:

* G belongs to the actual growth class C_F;
* P <_d P ⊕ B is a minimal strict d-closed extension;
* P is the exact strict d-closed hull of the old neighbours of B.

The increasing equivalence Fin(|B|) ≃o B induces a graph
isomorphism fixing P pointwise. Thus its pullback preserves
all finite induced subgraphs and their predimensions; in
particular it belongs to C_F. The existing normalized-type
constructor preserves minimal strict closure and the exact
old-neighbour support. If |P|+|B|≤K, then |B|≤K, giving an
actual member of the bounded finite local catalogue.

The theorem endpoints are:

* CFLocalCatalogue.growthSparse_orderedNormalize_iff
* CFLocalCatalogue.growthLocalType_of_orderedGraph
* CFLocalCatalogue.bounded_growthLocalType_of_orderedGraph

## Separate hostile proof checks

**A. Full induced structure.** A mere forward graph
homomorphism would not preserve the C_F growth inequality.
The equivalence preserves *both* adjacency and nonadjacency
for every pair, including pairs entirely in B and pairs
crossing the old boundary. Existing growthSparse_image_iff
uses induced injections, not only edge preservation.

**B. Actual support.** The old part is fixed pointwise by
the normalization. It must agree with the induced graph on
the *literal* support P. An arbitrary isomorphic relabelling
of P would not preserve a prescribed source embedding.

**C. Minimality and support.** The growth condition alone
does not imply that the graph is a permitted minimal local
type: the original strict-minimality and exact-support
hypotheses remain explicit and are transported by the
already certified normalization lemma. In particular,
a larger-than-minimal support would create duplicate
requests and invalidate the claimed canonical indexing.

**D. Numeric hypothesis.** The bound |P|+|B|≤K is an
explicit input here. The published Theorem 4.14 supplies
it for K(k)=F^{←}(2(k+1)), by minimal generation from
P plus any fresh vertex, but no Lean proof of that
particular analytic estimate is claimed by this PR.
For an arbitrary function K, completeness of the
catalogue would be false.

**E. Unfinished realization bridge.** The lemma starts
with a graph on the split carrier P ⊕ B. It has *not*
yet extracted such a graph from an arbitrary minimal
extension A <_d C and a prescribed induced embedding of
A into a tagged stage. That transport and the subsequent
countable local-response application remain independent
obligations.

## Validation policy

The Lean proof must compile at the final PR head and pass
the standard-axiom and placeholder checks. Only the exact
growth-normalization statements may then receive green
validation markers. The total countable genericity theorem
and functional root-recovery identity remain open.

These are five intentionally separated internal adversarial
mathematical reviews, not reports of external human referees.
