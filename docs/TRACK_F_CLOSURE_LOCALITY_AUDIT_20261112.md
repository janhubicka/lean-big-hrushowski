# Track F — locality of canonical component closures (12 November 2026)

Stacked on draft #445 (actual assembly of component orders).
Independent of the manuscript and its validation markers.
The notation is the established finite N_0 notation:
B is an actual SCC, C_B its successor closure and P_B=C_B\B.

## Submitted results

Fix a ranking r of actual SCCs. For each SCC choose a
bijective enumeration of its vertices, then concatenate the
orders in ranking order as in PR #445. The entire strict
comparison on distinct SCCs depends only on r. Within an SCC,
the comparison is exactly the chosen local enumeration.

If two families of component enumerations agree on all SCCs
contained in C_B, their assembled global orders have identical
induced enumerations on C_B. Consequently they make the same
choice on whether this induced enumeration is canonical for B
under the complete directed adjacency-code criterion.

Crucially, the other component orders are allowed to change
even when their components occur *before* B in the global order.
They are irrelevant unless they actually lie in C_B.

The new module \`N0ComponentClosureLocality.lean\` proves:

- \`assembleComponentEnumerations_distinctComponents\`
- \`inheritedComponentEnumeration_eq_of_component_agreement\`
- \`localCanonicalCondition_eq_of_component_agreement\`

These are statements about *literal induced enumerations* on
the original labelled closure, not about isomorphism types.

## Adversarial mathematical panel (internal checks)

1. **Closure referee.** The hypothesis concerns all SCCs
   *inside the genuine C_B*, not all components occurring earlier
   in a chosen linear extension. Unrelated earlier components
   must be irrelevant.
2. **Whole-component referee.** Membership of u in C_B and
   successor-closedness imply that its entire SCC lies in C_B.
   The proof explicitly invokes the SCC closure lemma.
3. **Within-component referee.** When u,v lie in the same SCC,
   their comparison is fixed by equality of that component's
   chosen enumeration, including comparisons of nonedges.
4. **Between-component referee.** When u,v lie in different
   SCCs, their comparison is fixed by r and is independent
   of all local ranks. This remains true for nonadjacent SCCs.
5. **Canonical-code referee.** The proof first establishes
   equality of whole induced enumerations of C_B. Therefore
   complete adjacency-code minima are preserved without
   assuming that the resulting canonical class is invariant
   under arbitrary changes of the lower-part ordering.
6. **Counterexample referee.** The conclusion is false if the
   ranking r is changed without retaining its relative order
   inside C_B, or if the local orders on components in C_B are
   allowed to differ. Neither is permitted by the hypotheses.
7. **Certification referee.** Exact named Lean axiom checks,
   source placeholder scan, and an independent finite test
   must all succeed on the exact PR head. This internal
   adversarial panel does not constitute external peer review.

## Finite regression

For every orientation of at most four vertices, every SCC ranking,
and every family of component orders, the independent test records
the induced enumeration on each actual C_B and whether its
complete directed code is minimal among same-old-position
enumerations. All families agreeing inside C_B must yield the
same record. Nontrivial examples change the 3-cycle order
outside the closure of an isolated singleton.

## Remaining counting step

Given any legal SCC ranking, process its SCCs successively.
For B, the local minimum-code choice depends only on orders
of components within P_B, together with B's own order.
Because every component of P_B is a strict proper successor of B,
these orders have been chosen already. The earlier local-fibre
theorem says the number of complete code-minimizing enumerations
over a fixed ordered P_B is g_A(B).

To obtain the exact global formula it remains to prove that
the restriction to the top SCC induces a bijection between
those local complete enumerations and the permitted next
component orders, for *every* previous history. Only then
can the existing uniform-dependent-history count be applied.

## Canonical assembly and reconstruction

The additional module \`N0CanonicalAssembly.lean\` defines
\`IsCanonicalComponentAssignment\` on actual SCC-order data
and proves:

- For a legal SCC ranking, the resulting assembled enumeration
  is globally canonical exactly when every inherited
  one-component closure enumeration satisfies its local
  canonical complete-adjacency-code criterion.
- Conversely every genuine globally canonical enumeration
  \(\mathrm{Fin}(|V|)\simeq V\) is exactly the concatenation of its
  recovered legal SCC ranking and its SCC restrictions.
  This is *equality* of labelled enumerations, using the earlier
  reconstruction theorem and injectivity of order relations.

The result is a **surjectivity theorem for actual canonical
assembly data**, not a proof of their cardinality. The remaining
requirements are uniqueness/injectivity of such data and uniform
cardinalities of admissible next-component choices. Neither
condition is silently inferred from finite tests.

Additional adversarial checks:

- The restriction inverse uses the original labels of V, not
  a choice of copies of the components.
- The ranking is legal because the original global
  enumeration is successor-first.
- The canonical predicate is imposed on full induced C_B,
  not merely the top SCC B.
- No counting statement is made from this existence theorem.
- Three new exact named theorem axiom checks are included.

## Actual inverse of the finite assembly data

The additional module \`N0AssemblyDataInverse.lean\` separates the
injectivity argument into two reusable facts:

1. Restricting an assembled global enumeration to each SCC gives
   back exactly the SCC enumeration that was supplied as input.
2. Ranking SCCs by first occurrence in the assembled global
   enumeration gives back exactly the original consecutive ranking.

The second point uses *all* comparisons between distinct SCCs
and the uniqueness of the order-preserving enumeration by a finite
ordinal. It does not use only the existence of an SCC interval
presentation. Thus the assembly map from a ranking plus one
enumeration per SCC to the actual labelled global enumeration
is injective.

These results, together with the existing reconstruction of every
SCC-interval enumeration, give the finite **geometric** bijection.
Together with the canonical assembly bridge, they also give
the bijection at the level of globally canonical data, once the
local admissibility predicate is imposed on the input data.

The cardinality of that restricted data set remains open. In
particular the product \(\ell(A)\prod_B g_A(B)\) is still not
declared a Lean theorem.

Additional adversarial checks:

- **Consecutive rank referee:** two distinct ordinal ranks
  cannot encode the same total component ordering. The proof
  invokes uniqueness of an enumeration by a finite ordinal,
  not merely equality of relative SCC comparisons.
- **Dependent carrier referee:** SCC restrictions are taken
  in their actual subtype vertex carriers, with no artificial
  copies or relabellings.
- **Automorphism referee:** internal SCC orders are recorded
  as labelled orders; quotienting by SCC automorphisms would
  destroy injectivity.
- **Surjectivity referee:** the inverse lemma applies to all
  actual SCC-interval orders; the canonical restriction is a
  separate property, not a consequence of mere intervality.
- **Certification referee:** three new exact named axiom checks
  are included. No Lean-validated status is claimed before
  the PR's exact-head CI passes.
