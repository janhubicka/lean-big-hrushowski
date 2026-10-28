# Combined adversarial audit: finite C_F request comparison
28 October 2026

## Verified inputs

- Complete row-major adjacency-bit matrices distinguish graphs on
  a fixed vertex type once every vertex occurs in the coordinate
  list. This is independent of C_F (source: PR #227).
- The literal increasing support tuple determines the named old
  support by finset extensionality (source: PR #229).
- The exact lexicographic request comparison is irreflexive and
  transitive; after equal supports and fresh sizes, it compares
  the complete local adjacency matrices (source: PRs #226/#228).

This clean branch merges the distinct declarations, their axiom
endpoints and their original hostile referee notes without
retaining conflicting root imports from parallel branches.

## Role-separated hostile checks

1. The graph-matrix lemma operates on the **same fixed vertex
   type and coordinate list**. A request with a different named
   support has a dependent local graph type; transport across
   that equality is still required.
2. The sorted support tuple must retain literal old vertex names,
   not only the induced old graph isomorphism type.
3. Fresh sizes precede adjacency codes in the paper's comparison,
   so two different sizes cannot be conflated even if their
   matrices have misleading common initial segments.
4. Row-major full matrices include old-old and fresh-fresh
   entries and reflect nonedges. A sparse edge-count code would
   be insufficient.
5. Request comparison transitivity is valid without code
   injectivity; this does not itself prove a strict total order
   on all request tags.
6. A separate proof must establish that equality of the full
   keys (support, fresh size, graph bits) forces equality of
   the complete dependent StageRequest records, including the
   old support and fresh graph code.
7. The finite comparison takes a chosen inherited LinearOrder
   on U as input; building the coherent recursive orders on
   U_n is not yet part of this integration.
8. The subsequent unique-level-lifting argument requires
   comparison-preservation under an increasing embedding
   of the old support tuples. Arbitrary request ranks from
   the earlier generic order lemma cannot replace this.
9. Full Lean CI of this **combined branch** is required even
   if all source branches separately compile, because the
   imports and exact axiom endpoints have changed.
10. The manuscript's order and root-recovery markers stay
    scoped to the exact currently verified statements. No
    green marker for the whole countable order is added.

These are independent internal mathematical adversarial roles.
