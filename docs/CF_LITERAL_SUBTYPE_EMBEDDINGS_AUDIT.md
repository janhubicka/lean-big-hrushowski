# Adversarial audit: literal closed-source subtype embeddings

22 October 2026

## Statement

Let X be a nonempty (possibly infinite) b-closed subset of the actual
countable C_F birth graph, and let

    e : {v : Vertex F K // v ∈ X} → Vertex F K

be an induced injective embedding on precisely its source subtype.
Assume e preserves/refects the birth-level preorder and strictly
preserves the finite ordinal order within each complete birth block
in X. Then complete b(v) values are transported exactly if and
only if complete R(v) and all defined H(S) values are transported
exactly, including preservation/reflection of the partial H-domain.

The proof uses an arbitrary total *function* f of the birth carrier,
obtained by evaluating e at a fixed genuine source vertex on inputs
outside X. No global embedding property of this extension is
postulated or used: all mathematical hypotheses and equalities are
on X, as verified in the prior source-local theorem.

## Hostile referee checks

1. **No invented target inhabitant.** A dummy value is chosen as
   the image of a *genuine* vertex of nonempty X; no arbitrary
   inhabitant of the birth carrier is assumed for F and K.
2. **Literal source type.** The theorem accepts a map from the
   actual membership subtype, not an isomorphic replacement or
   an enumeration of its vertices.
3. **No false global extension.** Outside X the total function f
   can be constant and noninjective. The previous theorem
   requires all hypotheses only on X.
4. **Induced nonedges.** The subtype embedding explicitly reflects
   nonadjacency; a homomorphism is insufficient for d-hull
   transport.
5. **Injectivity localization.** Restricting f to X reproduces
   the given e, so e's injectivity supplies precisely the local
   pairwise hypothesis.
6. **Level preorder.** Both preservation and reflection of
   birth-level comparison are required for the complete
   top-block and support formulas.
7. **Ordered fresh blocks.** Strict increasingness inside each
   complete block is assumed only for the source vertices;
   b-closedness ensures every member of a block met by X lies
   in X.
8. **Partial H-domain.** The right side includes equivalence of
   root-set domain predicates only for finite image sets
   generated from source arguments. It does not claim
   surjectivity on all ambient root sets.
9. **Exact values.** b, R and H are complete finite set-valued
   functions; the equivalence concerns equality of images, not
   one-sided containment.
10. **Empty-source case.** The theorem explicitly covers
    nonempty X; embeddings with empty source are trivially
    unique on vertex values, but the empty H-input and its
    value require an explicit final handling. Do not quietly
    conflate this case with an assumed inhabitant.
11. **Admissible-order bridge.** The paper's `<` must be
    shown to restrict to the chosen natural Fin n order on
    each fresh block. Lean's present theorem states that
    comparison explicitly and does not claim to have
    formalized the full global order on the birth carrier.
12. **Kernel/compilation.** Both exact endpoints must be
    exported, #print axioms audited, and all regression and
    placeholder checks passed before GREEN status.

These are role-separated internal adversarial proof reviews,
not independent external human referee reports.
