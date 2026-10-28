# Adversarial audit: complete dependent C_F request-code injectivity
28 October 2026

## Statement

For a fixed finite old graph carrying its inherited linear order,
the complete key of an actual StageRequest r consists of its
increasing named support tuple, fresh cardinality, and full
ordered row-major adjacency matrix.

Two equal keys force equality of the **entire dependent request
records**, not merely isomorphic local types. Thus the finite
RequestLexLt comparison is an irreflexive, transitive, strictly
total order on the literal request records.

## Ten hostile mathematical roles

1. **Literal support:** The first key component recovers P
   as an actual Finset of named old vertices. Replacing this by
   equality of support sizes would not permit dependent transport.
2. **Bounded index:** Equality of fresh natural sizes gives
   equality of the Fin indices of the bounded local code via
   Fin.ext. This keeps the actual bound K(P) unchanged.
3. **Same carrier:** Only *after* support and fresh size
   equalities are transported can the two local graphs be
   compared as GraphOn of one identical Sum support/fresh type.
4. **Full matrix:** The matrix enumerates the whole local graph,
   including edges within the fresh block and absent edges.
   The previously certified generic matrix injection gives
   equality of graphs, not just of old neighbours.
5. **Proof fields:** Local type certificates for admissibility,
   minimal strict d-closedness, exact support, old-base
   agreement and support closedness are propositions. Their
   equality follows by proof irrelevance once the graph and
   indices agree; no new mathematical choices remain.
6. **No duplicate requests:** Different actual supports or
   complete ordered local graphs are distinct keys; identical
   data correspond to one StageRequest despite different
   syntactic proof derivations.
7. **Strict totality:** Trichotomy uses the linear orders on
   support lists, fresh sizes and adjacency bits. In the
   all-equal case key injectivity is explicitly invoked.
8. **Irreflexivity/transitivity:** These were proved in merged
   #226/#230 independently of injectivity. No circular appeal
   to a preexisting order on requests is made.
9. **Order scope:** A strict linear order is now available at
   each fixed old stage, but the coherent recursive inheritance
   of the old-stage order and embedding naturality under
   level changes are *not* consequences of this local theorem.
10. **Kernel review:** The exact three declarations need a
    clean Lean build, all axiom endpoints, placeholder scan
    and regression checks; this paper's final global-order
    marker stays PARTIAL until the recursive stage construction.

The checks are role-separated internal adversarial scrutiny,
not independent human referees.
