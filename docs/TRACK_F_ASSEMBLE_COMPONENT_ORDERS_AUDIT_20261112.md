# Track F: assembly of actual component orders (12 November 2026)

Stacked on #441, which depends on #434; both are in the Track F
branch stemming from umbrella PR #270. No TeX or validation-marker
changes.

## Exact new finite theorem endpoints (pending CI)

Given a legal ranking r of the *actual* strongly connected
components, choose for each SCC B an enumeration
\(\mathrm{Fin}(|B|)\simeq B\). Assign to \(x\in B\) the inverse
position of x in B's enumeration.

New module \`N0AssembleComponentOrders.lean\` proves:

1. The ranks distinguish vertices inside each SCC, with no
   requirement to distinguish rank values in different SCCs.
2. Their pairwise comparisons on an SCC B are *exactly*
   those of the chosen component enumeration.
3. The lexicographic construction using component rank as
   its first key yields an actual bijective global enumeration
   of V by \(\mathrm{Fin}(|V|)\).
4. Every SCC is an interval of this global enumeration.
5. Every global comparison within B agrees with its
   prescribed local order, including nonedges.
6. If r extends the intrinsic successor dependency order,
   the assembled global enumeration is successor-first.

This is a concrete finite gluing theorem for component orders,
not a global canonical-order count.

## Seven adversarial referee roles (internal only)

- **Dependent carrier.** The local enumeration carrier is the
  actual subtype \(B\subseteq V\), not a copy of an abstract
  component isomorphism type.
- **Choice of generator.** No chosen vertex generates a
  separate component order; the component membership proof
  identifies all vertices in B's actual intrinsic SCC.
- **Rank collisions.** Rank labels may repeat across distinct
  SCCs. The composite key \((r(B),a(x))\) must nevertheless be
  globally injective.
- **Pointwise comparisons.** An SCC's entire labelled order
  is preserved, not only comparisons of adjacent vertices.
- **Uniqueness.** Different choices of SCC ranking or local
  SCC enumeration must not accidentally produce the same
  labelled global order. The finite regression exhaustively
  checks collision-freeness.
- **Direction.** A top SCC must follow its proper directed
  successors. Reversing this relation fails the
  successor-first test even when all intervals are present.
- **Certification.** Exact theorem axiom audit and source
  placeholder scan are required; the Python tests are not
  a kernel proof nor external human refereeing.

## Independent finite regression

The script enumerates all 653 orientations with at most four
vertices. For each, it exhausts all SCC rankings and local
SCC enumerations, constructs the resulting labelled global
order by concatenation, and checks the internal comparisons.
It also exhausts all labelled global orders and reconstructs
every SCC-interval order by recovering its component ranking
and its internal component orders.

Expected identity on those test objects:

\[
\#\{\text{all SCC-interval orders}\}
 =
\#\{\text{rankings and local SCC enumerations}\}
 =13730.
\]

Legal rankings generate exactly the successor-first SCC-interval
subfamily.

## Remaining mathematical gap

The direct component concatenation currently allows *every*
local SCC enumeration. The manuscript imposes the selected
complete-matrix representative on the full one-component
closure \(C_B=P_B\sqcup B\), where the order on \(P_B\)
is inherited from previously chosen components. The canonical
local choices form a fibre of cardinality \(g_A(B)\).
The next proof is to implement this history-dependent
selection using the new global assembly and induced-closure
restriction, establish compatibility of successive choices,
and prove the resulting bijection. This, not the unqualified
component concatenation, is the missing proof of the finite
\(\ell(A)\prod_Bg_A(B)\) degree formula.
