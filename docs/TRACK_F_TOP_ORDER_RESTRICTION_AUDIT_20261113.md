# Track F — recovering the actual top SCC order (13 November 2026)

Stacked on Track F PR #504, which proves that reordering the
top SCC fixes all positions of the old part in C_B.
No TeX or validation-marker changes.

## New finite proof interface

For an actual SCC B of the finite orientation, let x be its
chosen component generator, and let C_B be its successor
closure. An arbitrary finite enumeration of C_B induces
a unique enumeration of the *actual labelled* subtype B:
compare the positions of B's vertices in the full enumeration,
then use the unique finite order-isomorphism
\(\mathrm{Fin}(|B|)\simeq B\).

The module \`N0StageTopOrderRestriction.lean\` defines
\`topOrderFromClosure\` and verifies literal equality of every
internal B comparison, including nonedges.

Its main theorem states that if t is a chosen internal
enumeration of B and we update the full SCC-order assignment
at B to t, then restricting the induced C_B enumeration
back to B recovers **exactly t**.

As a consequence the map

\[
 t\longmapsto
 \operatorname{ind}_{C_B}
    \bigl(\operatorname{assemble}_r(\mathbf e[B\mapsto t])\bigr)
\]

is injective on all labelled B orders, without requiring
canonicality or even a legal SCC ranking.

## Internal adversarial referee panel

1. **Actual carrier.** The new order is on B as a subtype of
   the original labelled vertex set. No isomorphic copy of
   B and no quotient by automorphisms is used.
2. **Closure inclusion.** B lies inside C_B by successor
   closure, so restriction is defined for every vertex of B.
   This must not be replaced by a graph-theoretic adjacency
   assumption.
3. **Nonedges.** The order comparison equivalence quantifies
   over all pairs of vertices of B, including nonadjacent ones.
4. **Rank independence.** Injectivity holds for any SCC
   ranking, including illegal rankings; legality is needed
   later only to put P_B before B.
5. **Dependently typed update.** The proof retrieves the
   update at the exact actual SCC B and not at another SCC
   with an isomorphic graph.
6. **Distinctness.** Different internal B enumerations must
   yield different local C_B enumerations, even if global
   ambient positions are disturbed by unrelated SCCs.
7. **Certification.** Dedicated exact-head Lean compilation,
   named axiom inspection, placeholder scan and independent
   exhaustive finite tests are required. This panel consists
   of internal role-separated checks, not external reviewers.

The negative finite control uses a 3-cycle plus an isolated
vertex: moving the isolated vertex changes the ambient
enumeration without changing the order induced on the cycle.
This is why the proof must use restriction to C_B, not
absolute global vertex positions.

## Open mathematical direction

Surjectivity remains: let f be *any* complete enumeration
of C_B with the already prescribed old positions. Let t
be the order which f induces on B. We must prove that
updating the global SCC assignment at B to t produces
exactly f on C_B.

The proof should compare the old-old, new-new and cross
pairs. Old-old comparisons agree by PR #504; new-new
comparisons agree by the present top restriction theorem;
and all old vertices precede B in both local enumerations.
The earlier enumeration uniqueness lemma then gives equality.

Once proved, the complete fixed-old enumeration set
is bijective with the set of possible labelled B orders,
and restricting to its complete-code-minimum class
yields precisely g_A(B) canonical next choices.
The finite global product formula and the infinite
Ramsey theorem are not claimed here.
