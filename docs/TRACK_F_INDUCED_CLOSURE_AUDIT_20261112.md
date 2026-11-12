# Track F: inherited orders on actual successor closures (12 November 2026)

Parent branch: Track F #270. Builds on merged #413 and #425.
New module: \`BigHrushovski/N0InducedClosureOrders.lean\`.
No changes to the TeX manuscript or to its validation markers.

## Scope of proposed Lean results

Given a complete labelled enumeration \(e:\mathrm{Fin}(n)\simeq V\)
and a finite subset \(S\subseteq V\), the module uses the
finite-order isomorphism of the inherited order on \(S\) to define
\(\operatorname{ind}_S(e):\mathrm{Fin}(|S|)\simeq S\).
It proves precisely

\[
\operatorname{ind}_S(e)^{-1}(u)<\operatorname{ind}_S(e)^{-1}(v)
\iff e^{-1}(u)<e^{-1}(v)
\quad(u,v\in S).
\]

This yields (i) compatibility with nested restrictions \(S\subseteq T\),
and (ii) equality of induced enumerations whenever two ambient
enumerations have the same comparison relation on \(S\).

For an actual SCC \(B\), instantiate \(S=C_B\) and prove that
successor-first global orders place all of \(P_B=C_B\setminus B\)
before \(B\) in the restricted order. Consequently \(P_B\) is an
initial segment of \(\operatorname{ind}_{C_B}(e)\).

A concrete finite candidate for permitted \(N_0\) orders now requires:
SCC intervals, successor-first comparisons and the genuinely
inherited enumeration on every \(C_B\) attaining the canonical
minimum complete adjacency-code class. A theorem maps each
such local enumeration into the previously certified class of
labelled local orders. Finally the number of distinct labelled
global order relations is proved equal to the number of such
global enumerations.

**Strict boundary:** no bijection has been proved from arbitrary
compatible families of component-local canonical orders to all
finite global canonical orders. In particular the equality with
\(\ell(A)\prod_B g_A(B)\) is not asserted as a Lean theorem,
and the infinite \(N_0\) Ramsey theorem remains open.

## Adversarial referee panel (independent reasoning roles)

1. **Order restriction.** Restriction ignores all unrelated
   ambient vertices; changing their positions cannot change the
   induced order on \(S\). The order on \(S\) is defined via the
   canonical finite *order isomorphism*, not a choice of arbitrary
   labels.
2. **Labelled versus unlabelled referee.** Pairwise comparisons
   are on the same fixed labelled vertex type. Equality of
   induced enumerations is literal, not equality up to an
   isomorphism or an automorphism.
3. **Component-closure referee.** The restriction uses the
   actual \(C_B=\operatorname{scl}(B)\), including the entire
   lower part \(P_B\); the induced orientation, not the ambient
   stabilizer, defines \(g_A(B)\).
4. **Initial-segment referee.** \(P_B\) is an initial segment
   inside \(C_B\), not necessarily inside the ambient graph.
   Correctness requires successor-first; it is false for an
   oriented edge listed source before sink.
5. **Canonical-code referee.** The whole directed adjacency
   matrix (positive and negative entries) determines the
   canonical class; the global canonical condition is not
   automatically true of an arbitrary ordering.
6. **Surjectivity referee.** Forward mapping into each
   component's canonical local class does not imply that every
   tuple of chosen local classes glues to a permitted global
   order; this missing direction is explicitly excluded.
7. **Certification referee.** Passing finite Python regression
   is evidence but not an independent human refereeing result
   or a Lean kernel proof. Require exact-head Lean build,
   named-axiom audit and placeholder scan before promotion.

The regression independently checks literal pairwise order
restrictions for all subsets of all 653 small orientations,
nested restriction compatibility, lower-part initiality in
successor-first cases, and global lexicographic-minimum membership.
The expected 1,764 globally canonical labelled orders is only
a finite regression target, not a theorem about arbitrary finite
objects.

## Next step

Formalize an explicit gluing map from successive permissible
orders on the actual SCCs, show that the induced enumeration on
each \(C_B\) agrees with the prescribed local canonical class,
and prove uniqueness and existence. Then apply the existing
dependent-history cardinality lemma to count the finite orders.
Only after proving this bijection can the finite expansion
formula receive a validation marker.
