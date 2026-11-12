# Track F — exact canonical finite-order data count (12 November 2026)

Base: Track F integration PR #270. No TeX or manuscript
validation-marker changes.

## Proposed exact finite statements

Define \`canonicalComponentOrderData\` to be the finite set of pairs
\((r,\mathbf e)\), where r is a legal consecutive ranking of the
*actual SCCs* and \(\mathbf e\) is a bijective enumeration of
each actual SCC such that the global concatenation satisfies
the complete local canonical-code condition on every
one-component successor closure \(C_B\).

The existing exact finite assembly and its inverse (merged #445
and #470) give a **literal finite bijection** with globally
permitted labelled enumerations. The new module
\`N0CanonicalDataCardinality.lean\` makes this cardinal statement
explicit. It also identifies the number of actual strict order
relations (not just enumeration records) with that cardinal.

It decomposes the canonical data set into a disjoint union of
its fibres over the legal SCC rankings. Thus

\[
|\mathcal O_{\mathrm{can}}(A)|
=\sum_{r\text{ legal}}|\mathcal E_r|,
\]

where \(\mathcal E_r\) is the set of component-enumeration families
that yield canonical global orders at fixed ranking r.

A further theorem makes the remaining hypothesis explicit:
if **for every legal r**,

\[
|\mathcal E_r|=\prod_B g_A(B),
\]

then the number of actual canonical labelled orders equals
\(\ell(A)\prod_B g_A(B)\). This is a conditional theorem.
**The uniform-rank fibre hypothesis is not yet proved in Lean.**
It must not be hidden in a validation marker or a claimed
big Ramsey degree.

## Independent adversarial referee panel

1. **Actual-order referee.** The codomain is the real finite
   set of labelled strict linear orders on V, not isomorphism
   classes or synthetic numeric choice records. The proof uses
   the verified injectivity of \`OrderBefore\`.
2. **Inverse referee.** The finite data-to-order map is
   injective because the SCC ranking and each SCC enumeration
   can be recovered exactly. Surjectivity uses the canonical
   global reconstruction lemma, not the product formula.
3. **SCC referee.** The ranking ranges over strongly connected
   components of the actual finite orientation, not over
   arbitrary chronological blocks. The legal predicate uses
   intrinsic proper-successor precedence.
4. **Disjointness referee.** The fibres over distinct legal
   rankings do not overlap as data pairs, irrespective of
   whether the underlying component assignments coincide.
   This justifies \`Finset.card_biUnion\`.
5. **Locality referee.** The global canonical predicate tests
   the complete directed adjacency code of each *induced*
   \(C_B\); the lower part need not be a global initial segment
   and no unrestricted local permutation is declared canonical.
6. **Uniformity referee.** The fibre count for each rank is
   displayed as a hypothesis, not smuggled into an equivalence.
   A separate recursive proof must identify each reachable
   next-component order choice with a canonical top-component
   fibre of cardinality \(g_A(B)\).
7. **Certification referee.** The exact-head Lean build,
   named-axiom inspection, placeholder scan, and independent
   exhaustive finite enumeration must all pass. This
   role-separated audit is not independent human peer review.

## Independent finite regressions

The Python regression exhausts all 653 orientations on up to
four labelled vertices, all SCC rankings and all internal SCC
permutations. For each it compares the image of legal canonical
data with independently enumerated actual canonical vertex
orders. It checks that the sum over ranking fibres equals
the actual order count and, separately **only computationally**,
that all small fibres have the expected product cardinality.

Negative controls reject interleaving a 3-cycle SCC with an
unrelated singleton, and reject nonminimal orderings of the
directed triangle.

## Next precise obligation

For every legal ranking r and every *reachable* previous
sequence of SCC orders, prove the number of admissible orders
of the next SCC B is exactly g_A(B). The merged
\`N0CanonicalTopOrderFibres\` counts the local candidates.
The remaining work is to identify these candidates with the
actual global extension fibre for each history. The
reachable-history induction in separate PR #482 then counts
the full assignment families. Infinite Ramsey theory remains
a separate part of Track F.
