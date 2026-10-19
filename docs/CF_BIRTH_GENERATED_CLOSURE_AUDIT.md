# Adversarial audit: finite generation of the auxiliary C_F block closure

19 October 2026

## Mathematical claim

For any finite set S of actual birth-labelled vertices, there exists a **least finite** set C containing S and closed under all complete birth-block/support values b(v)=P_B∪B. The leastness is with respect to every finite b-closed superset in the **whole countable birth graph**, not only supersets in a chosen stage.

Choose N with S contained in the finite stage image U_N. Birth-level characterization gives v∈U_N precisely when birth(v)<N. Hence U_N itself is b-closed: complete blocks preserve the birth index, and all old support vertices have strictly smaller birth indices. The family of b-closed sets is closed under finite intersection. Intersect all b-closed subsets of U_N containing S. This intersection is finite and closed.

For global leastness, any other finite b-closed T containing S may extend beyond U_N. Its intersection T∩U_N is b-closed and remains a candidate. Therefore the selected intersection is contained in T.

## Eight hostile checks

1. **Finite ambient:** U_N is a finite set of actual birth-labelled vertices. A finite input S lies in some U_N by the already certified finite stage coverage theorem; no countability assumption is silently replaced by a finite universe.
2. **Birth index:** Old stage vertices satisfy birth(toVertex n u)<n. New vertices of a fixed request have birth index exactly n. This proves closure of U_N under the full b-value.
3. **Same block:** Distinct fresh ordinals of one request share the same birth level and request tag. Replacing literal request records with graph isomorphism types would make this property insufficient.
4. **Exact support:** A request's support is a subset of its *actual old stage*; each support vertex is born before the request level. The support may be larger than the immediate neighbour set and must not be replaced by it.
5. **Intersections:** Being b-closed forces complete values. If a vertex lies in both closed sets, its entire value lies in both. The empty intersection family returns the finite ambient U_N, which is itself b-closed.
6. **Global minimality:** Intersecting only b-closed subsets of U_N would *not* imply leastness among all global b-closed supersets unless the latter may first be intersected with U_N. This reduction is explicit.
7. **Uniformity:** The proof is parameterized by arbitrary growth F and size bound K; neither analyticity of F nor free amalgamation of the restricted growth class is invoked. These were needed for the graph class construction, not for its finite block closure algebra.
8. **Formalization boundary:** This supplies finite generated b-closure, but not the root set R(v), its exact finite reachability in the tagged tower, the equation H(R(v))=C(v), or naturality of all H-values under embeddings. Those remain open.

The audit uses independently motivated hostile mathematical roles, not external referees. The proof receives GREEN only after the complete integrated Lean build, exact axiom audit and no-placeholder scan.
