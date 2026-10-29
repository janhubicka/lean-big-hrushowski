# Adversarial audit: complete adjacency matrix naturality

29 October 2026

## Verified statement sought

For an induced map f between finite graphs and an ordered source
coordinate list xs, the complete row-major adjacency matrix of
the source equals that of the target on xs.map f. The result is
generic and reusable by both C_0 component presentations and C_F
ordered local request codes.

## Separate hostile checks

1. **Edges and nonedges.** A graph homomorphism alone is not enough.
   The theorem assumes G.adj x y ↔ H.adj (f x) (f y),
   so every zero and one in the full matrix is preserved.
2. **Repeated coordinates.** The list may repeat vertices. The
   proof works on the entire row-major Cartesian square, with
   no assumption of distinctness or completeness. The earlier
   injectivity theorem separately requires that every vertex
   occurs in the coordinate list.
3. **Noninjective maps.** The algebraic matrix identity itself
   does not require injectivity. If an induced map identifies
   vertices, the equality still holds on the specified list;
   this does not imply that such a map is an embedding.
4. **Order and named supports.** The matrix identity is
   conditional on the *target coordinate list* being exactly
   xs.map f. It does not prove that sorting a transported named
   support commutes with an arbitrary partial map. The latter
   requires strict monotonicity on the selected old support and
   remains a separate finite lifting step.
5. **Empty cases.** The empty list produces the empty matrix;
   no inhabitedness or nonempty extension is assumed.
6. **Lean kernel.** Three exact axiom endpoints, full build,
   placeholder scan and existing finite regressions are
   required before treating these statements as verified.

These are adversarial mathematical checks within the project,
not independent external human referee reports.
