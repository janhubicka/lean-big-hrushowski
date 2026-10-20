# Adversarial audit — exact old neighbours of an actual tagged birth block

20 October 2026

**Claim.** In the countable C_F birth graph, for a request r at level n, every edge from a fresh vertex of r to an old vertex of stage U_n has its old endpoint in the *literal named support* P_r. Thus the old-neighbour set of the whole fresh block, computed in U_n, is exactly its old-neighbour set in P_r. The same equality holds for every intermediate old set A with P_r⊆A⊆U_n.

## Nine hostile checks

1. **Literal tags:** Fresh vertices are identified by the exact dependent pair (request r, ordinal i), not an isomorphism type; two different requests cannot share the same fresh vertex.
2. **Complete boundary:** The finite tagged_old_fresh_adj_iff theorem is an equivalence of adjacency, so the reflection of *absent* edges outside support is not assumed but established.
3. **Birth mapping:** Actual old stage vertices are mapped by Sum.inl, fresh block vertices by Sum.inr. Their `toVertex` images carry the same birth names in the countable limit.
4. **Inducedness:** Transfer uses `countableGraph_stage_induced` (adjacency iff); an arbitrary graph homomorphism could create later cross edges and would not suffice.
5. **Support scope:** The conclusion says all old neighbours lie *in P_r*, not that every vertex of P_r is adjacent to the block. The support is the d-closure of its actual old neighbours.
6. **Sets rather than points:** The oldNeighbourSet equality ranges over the *entire fresh block*, not just its first vertex, ensuring the complete b-value can eventually be recovered.
7. **Intermediate old subsets:** Restriction from U_n to any A containing P_r leaves the neighbour set unchanged; no claim is made about subsets omitting some of P_r.
8. **Countable ambient:** No new edges appear among old stage vertices and the block in later stages because the old finite stage is induced in the countable graph. This is a certified theorem, not an implicit feature of direct limits.
9. **Remaining embedding boundary:** This proves the needed no-cross relation, but identifying C(v)\B(v) with an old subset of U_n uses the top-birth-level decomposition (separate PR #205). Full order/partial-H-domain equivalence is not established here.

These are independent mathematical roles reviewed internally, not claims of external referees. Green markers require full Lean build, axiom scan, placeholder check and regression tests.
