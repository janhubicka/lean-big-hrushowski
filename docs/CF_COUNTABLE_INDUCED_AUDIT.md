# Adversarial audit: induced finite stages in the countable C_F graph

16 October 2026

## Main claim

The countable graph on birth-labelled vertices was defined by
an existential finite-stage edge witness. Every canonical map
from U_n into this graph preserves and **reflects** adjacency:

    E_limit(birth_n(a), birth_n(b)) iff E_n(a,b).

Forward preservation is immediate from the witness n. For
reflection, an arbitrary witness in U_m is compared with
the original vertices at a common later stage U_max(n,m).
The old embeddings are induced. Their birth labels do
not change, and stage-to-birth injectivity forces the two
representatives of each vertex to agree at the common stage.

## Five independent hostile mathematical checks

1. **Witness dependence.** The countable graph's existential
   edge witness may occur at a much later stage than either
   vertex's birth. The proof must show that the witness can be
   reflected back to the requested old stage. Merely knowing
   that both vertices appear at finite stages does not do so.

2. **Directedness.** The natural-number indexing is directed
   by the common upper bound max(n,m). Canonical embeddings
   embedToLater are built from the actual k-fold Sum.inl
   inclusions, not chosen abstract graph isomorphisms.
   The arithmetic identity n+(m-n)=m needs to be used
   consistently when transporting dependent carrier types.

3. **No duplicates.** If two representatives in U_max(n,m)
   have equal birth labels, the previously audited
   toVertex_injective forces literal equality. Without
   this step a later edge could be witnessed between
   incompatible representatives and create a false
   edge between two earlier vertices.

4. **Nonedge reflection.** The iterated embedding lemma is
   an adjacency *equivalence*, not a forward implication.
   This is essential for transferring finite predimension
   and d-closedness to the ambient countable graph.

5. **Remaining status.** Even with full inducedness, the
   countable graph is not yet identified with M_F:
   one must prove that every finite set lies inside
   one common later stage, that d-closed stage inclusions
   become globally d-closed in the limit, that all finite
   induced subgraphs satisfy the F-growth inequality under
   the stated class hypotheses, and that the actual local
   request catalogue realizes each finite minimal
   d-closed extension over the named base.

The exact statement may receive a green Lean marker only
after its final CI run checks the proof, standard axioms
and absence of placeholders. The five roles above are
separate internal adversarial analyses, not independently
spawned external human referees.
