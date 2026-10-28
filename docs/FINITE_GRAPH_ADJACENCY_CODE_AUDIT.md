# Adversarial audit: finite complete adjacency codes
28 October 2026

## Scope

For any vertex type W and any list xs containing every vertex,
enumerate the ordered pairs (u,v)∈xs×xs row-by-row and record 1 if
G.adj(u,v), otherwise 0. The resulting bit list determines a simple
graph G uniquely. The list xs need not have distinct elements.

The proof extracts equality of each coordinate from equality of
mapped lists and uses completeness of xs to obtain equality of
adjacency on all ordered pairs. Symmetry/irreflexivity proofs in
GraphOn are propositions, so equality of adjacency predicates
gives equality of the GraphOn structures.

## Independent adversarial referee roles

1. **Nonedges:** The matrix includes zero bits for absent edges.
   Equality of only the positive edges is enough for graph
   equality but cannot be substituted without a separate proof.
2. **Directed coordinate positions:** Both (u,v) and (v,u) are
   included; undirected symmetry may make entries redundant but
   does not invalidate injectivity.
3. **Repeated coordinates:** Only coverage is assumed; no
   injectivity of the coordinate enumeration is used. Repeats
   merely duplicate already determined entries.
4. **Empty vertex type:** If W is empty, every pair list is
   empty; GraphOn has at most one adjacency relation on W,
   so the proof remains valid.
5. **One-element type:** Irreflexivity forces the only matrix
   bit to zero; the code correctly distinguishes the unique
   graph without assuming a nontrivial edge.
6. **Source equality:** Both codes must use the same ordered
   coordinate list. Permuting one matrix independently would
   not allow pointwise comparison of entries.
7. **Full domain:** Every vertex must occur at least once.
   Omitting one vertex permits graphs with different incident
   edges to have the same code; this hypothesis is essential.
8. **Graph structures:** The proof uses proof irrelevance of
   symmetry and irreflexivity certificates. It does not
   equate graph objects merely from their edge cardinalities.
9. **Reuse:** The result is independent of C_F growth, supports,
   orders, or predimension, and can be used by both C_F
   ordered local type codes and C_0 component graph codes.
10. **Manuscript boundary:** This supplies the graph-code
    injectivity over a fixed coordinate type. Proving that two
    complete *request* codes determine the same named support
    and fresh size still requires transporting between their
    dependent local graph types.
11. **Kernel:** Only two exact theorem endpoints are promoted
    after full CI, #print axioms, no-placeholder checks and
    downstream regressions.

All referee roles are internal, not independent external reviewers.
