# Full C_F auxiliary b-value recovery from R,H and birth levels

22 October 2026

## Target theorem

Suppose f is an injective *induced* self-map of the actual tagged
countable C_F birth graph, preserving and reflecting equality of
birth levels. Suppose also that it preserves the complete set-valued
R(v) and each defined H(S) (S a finite set of genuine block roots).
Then it preserves complete auxiliary b(v) values, with equality:

    f[b(v)] = b(f(v)).

This is not asserted for a mere graph homomorphism or a map that
preserves R,H-values only by inclusion.

## Reusable finite reconstruction

Write C(v) for the least finite b-closure of v; B(v) for its entire
birth block and P(v) for its named old support. Existing kernel-checked
results identify B(v) with the top birth-level part of C(v) and P(v)
with the finite d-hull of all neighbours of B(v) inside C(v)\B(v).
The new module first proves the following independent map lemmas:

- f[C(v)]=C(f(v)) and level equivalence imply f[B(v)]=B(f(v));
- under injectivity, f[C(v)\B(v)]=C(f(v))\B(f(v));
- induced adjacency and finite d-hull naturality then yield
  f[P(v)]=P(f(v));
- hence f[b(v)]=b(f(v)) for the complete union P(v)∪B(v).

Finally, H(R(v))=C(v), exact R-value preservation and exact H-value
preservation give f[C(v)]=C(f(v)), completing the converse direction
under these explicit hypotheses.

## Eleven independent hostile mathematical checks

1. **No quotient:** All sets and maps use the literal birth carrier.
   No equivalence relation on roots or isomorphic replacement appears.
2. **Source container:** Exact C-value image equality is essential
   to recover target B(v); mere inclusion cannot yield the reverse
   inclusion for the whole target block.
3. **Levels:** Reflection of level equality is required for inverse
   membership in B(v), not just forward preservation of levels.
4. **Finite-set difference:** Exact transport of C(v)\B(v) requires
   injectivity; otherwise a source vertex outside B may collapse
   onto one inside B.
5. **Old neighbours:** Use the complete block B and the full old
   complement C(v)\B, not a single root or graph-neighbourhood of v.
6. **Inducedness:** Both edges and nonedges are reflected by the
   finite map before applying dClosedHull_image.
7. **No infinite predimension:** The support closure is computed in
   the finite induced subgraph on C(v). Global strict closure was
   already used to justify this finite calculation.
8. **Partial H-domain:** H-value transport is assumed *only* on
   finite sets of genuine roots, not on all finite subsets. R(v)
   consists of roots by the earlier certified theorem.
9. **Full values:** Every value equation is equality of finite
   image sets, never merely preservation as subset inclusion.
10. **Source-substructure scope:** The formal f is currently a
    total self-map of the birth carrier. Applying this to arbitrary
    finite closed source embeddings needs an induced source-subtype
    version; do not promote full embedding equivalence yet.
11. **Order compatibility:** Equality of birth levels is the part
    of the level preorder needed for RH-to-b. The reverse b-to-RH
    direction additionally requires preservation of first vertices
    from the admissible order of each recovered block.

These are role-separated internal hostile reviews, not external
human referees. Nine exact theorem endpoints must pass full Lean
build, axiom, no-placeholder and regression CI before marked GREEN.
