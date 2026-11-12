# Track F — canonical choices are distinct orders of the top SCC (12 November 2026)

Based on the Track F integration branch, using the previously
merged local canonical enumeration and order-relation results.
No manuscript or validation-marker changes.

## Finite theorem (submitted for Lean certification)

Let B be an actual strongly connected component of a finite
orientation, C_B its complete successor closure and
P_B=C_B\B its strict lower successor part.

Fix an enumeration e0 of C_B putting all vertices of P_B first.
The earlier canonical code fibre consists of full enumerations
of C_B fixing the individual old positions and attaining the least
complete directed adjacency code.

New module \`N0CanonicalTopOrderFibres.lean\` restricts each member
to the *actual labelled complement of P_B* (identified by a lemma
with B) and counts the resulting strict orders.

The claimed exact identity is

\[
\left|\{\text{top-component orders arising from the canonical fibre}\}\right|
=g_A(B)
=|\operatorname{Aut}(A[C_B])_{(P_B)}|.
\]

The essential injection is elementary. Two full local enumerations
in the canonical class agree at all old positions; each has all
old vertices before the new ones. If they give the same order to
the new vertices, then they agree on all comparisons in C_B and
hence are the same enumeration of that labelled closure. This
isolates the map from full local orders to actual next-component
choices, which was missing from earlier count statements.

## Internal adversarial referee panel

1. **Correct factor referee.** Use the stabilizer in the induced
   orientation on C_B, not an ambient automorphism group.
2. **Actual top referee.** The complement of P_B inside C_B
   is exactly B as a *set of original labelled vertices*.
   Replacing it by an arbitrary isomorphic copy could change
   what is being counted.
3. **Old-position referee.** Agreement of the *relative order*
   on P_B alone does not determine the global interleaving.
   The canonical fibre fixes the old positions pointwise,
   preventing this ambiguity.
4. **Initial-segment referee.** Every induced closure of a
   successor-first global order has P_B before B. This
   hypothesis yields a short proof by splitting comparisons
   into old-old, new-new and cross pairs. The stronger
   injectivity fact without initiality is true under fixed
   old positions but is not needed here; it is not claimed
   false.
5. **Internal order referee.** The top order must distinguish
   every labelled vertex comparison, including nonedges.
   Counting only adjacency words could identify distinct
   vertex orders.
6. **Surjectivity referee.** The argument counts orders
   *arising from the local canonical fibre*. It does not
   show that every arbitrary top order is permitted; the
   actual global recursion must choose from the specified
   fibre over the previously ordered P_B.
7. **Certification referee.** The exact theorem axiom printout,
   no-placeholder scan and independent finite regressions
   are required at the exact PR head. The present role
   analysis is not external human refereeing.

## Independent regression

For every finite orientation on at most four vertices and
every SCC B, enumerate all bases of C_B with P_B first.
Compute complete directed adjacency matrices, the true
pointwise stabilizer order, and the minimum-code local
enumeration class. Project every canonical enumeration to
its labelled top order and confirm that the projection is
injective and has exactly g_A(B) elements.

The negative test fixes the internal orders of the old
and new parts but allows their *positions* to interleave.
It demonstrates why the fixed-position hypothesis, not just
matching relative orders, is essential in general.

## Remaining proof obligation

For each legal SCC ranking, inductively append an order
of B chosen from the local canonical fibre over the order
previously established on P_B. The new result supplies the
correct number of next-component orders. What remains is
the existence and uniqueness of the full enumeration
extending every compatible sequence of such choices and
verification that these histories are precisely the globally
permitted orders. The existing dependent-history counting
lemma would then yield the product.
