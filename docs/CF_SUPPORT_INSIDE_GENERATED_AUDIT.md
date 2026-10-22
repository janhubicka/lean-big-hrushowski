# Intrinsic C_F support recovery in the finite generated closure

22 October 2026

The target theorem is

    P_B = cl^d_{C(v)}(N_{C(v) \ B}(B))

for a vertex v in the actual tagged fresh block B, where C(v) is the
*least finite auxiliary b-closed* set containing v. The closure on
the right is taken in the finite induced graph on C(v), not in
the entire countable graph, and the neighbour set is computed
against the complete fresh block B, not a single representative.

## Adversarial referee roles

1. **Birth-level cut.** The verified decomposition C(v)=B∪cl_b(P_B)
   implies C(v)\B lies in the previous birth stage; no later blocks
   can enter through support closure.
2. **Support included.** Every vertex of P_B lies in C(v) by b-closure
   and is born strictly earlier than B, so P_B⊆C(v)\B.
3. **Boundary edges.** No fresh vertex of B has an old neighbour
   outside P_B. Use exact induced old-fresh adjacency on the actual
   request tags, not a homomorphism or a finite proxy.
4. **Complete neighbour set.** Neighbours are computed for the whole
   block B, because a block may have support neighbours on different
   fresh vertices.
5. **Finite closure.** C(v) is a finite globally strictly d-closed
   container. Hence the least global H-hull of a subset of C(v)
   agrees with its finite d-closed hull inside C(v).
6. **Support exactness.** The verified local type guarantees that the
   old neighbours globally d-generate P_B; no assertion of
   decomposable or graph-neighbour closure is substituted.
7. **Potential empty support.** All inclusions remain meaningful for
   an empty P_B and an initial birth level; no witness of a root or
   support vertex is assumed.
8. **Source labels.** The support, fresh block, and generated closure
   are the actual birth-carrier Finsets; no renumbering or isomorphic
   replacement appears in the conclusion.
9. **Embedding scope.** An induced isomorphism of finite C(v)
   intervals transports the computed support *once* C(v) and B(v)
   are known to be mapped exactly. Those exact image equalities
   and the partial H-domain still require a combined embedding proof.
10. **Kernel audit.** The manuscript marker must remain PARTIAL until
    the exact module and #print axioms endpoint compile under the full
    root import, with no placeholders and all regression tests.

Internal hostile reviews are not independent external referees.
