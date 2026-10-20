# Adversarial audit: top birth block of a generated closure

20 October 2026

## Statement

Let v be a vertex born at level n in the literal request-tagged block B, with named old support P. The *least finite b-closed* generated set satisfies

  C(v) = B ∪ cl_b(P).

Every vertex of cl_b(P) is born at a level strictly below n. Thus the vertices of C(v) at the same birth level as v are **exactly** B. This makes B intrinsically recognizable from the full generated closure and the level preorder. There is no need to define B by an equality of entire root sets or introduce an extra equivalence relation.

## Nine adversarial mathematical checks

1. **Exact b-value:** The complete b(v) is P∪B, not just the single vertex or graph-neighbourhood. Saturation of the tagged request forces all its fresh ordinals.
2. **Old support:** P lies literally inside stage U_n, and every vertex in the *generated* closure of P remains in U_n because the finite stage is b-closed.
3. **No same-level ancestors:** Dependencies point to old supports and thus strictly decrease birth levels. The closure of P cannot create any fresh vertex of level n.
4. **Fresh block tag:** All vertices of B share exactly n and the same request tag, though their ordinals differ. Distinct requests on level n must not be identified by graph isomorphism.
5. **Candidate closedness:** The finite candidate cl_b(P)∪B is b-closed because cl_b(P) is closed and every b-value from B is P∪B; this is not implied merely by it containing b(v).
6. **Leastness both ways:** C(v) is contained in the candidate by its universal leastness. Conversely, C(v) contains P∪B by b-closedness and therefore cl_b(P), again by leastness.
7. **Stage condition:** U_n may be empty (including n=0); all arguments use actual finite birth stage images and work for empty old supports.
8. **Manuscript use:** This certifies that B(v) is the *top birth-level part* of C(v). The order language must still preserve/reflect levels to transport this characterization under embeddings.
9. **Kernel assurance:** Eight exact axiom endpoints, full Lean build, no-placeholder scan and regressions must pass before a GREEN manuscript marker. This theorem does not by itself prove equivalence of R,H and b embeddings or complete reflection of H's partial domain.

Reviews are role-separated internal hostile checks; they do not claim independent external referees.
