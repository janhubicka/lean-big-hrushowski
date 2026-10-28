# Adversarial audit: recursively inherited C_F orders

28 October 2026

## Exact theorem scope

The actual tower has finite carriers `U_(n+1) = Sum U_n (FreshAt n)`,
and each fresh vertex consists of a literal request tag and its ordinal
within the request's increment. Define the linear order recursively:

- `U_0` has the unique order on its empty carrier;
- preserve the old `U_n` order, with all old vertices first;
- compare fresh tags by the canonical **strict lexicographic** ranks of
  support tuples, fresh sizes and complete adjacency matrices;
- within a fixed request block, compare the original `Fin` labels.

The rank is **not** `Fintype.equivFin` but the number of preceding
literal request records. In particular, by the already-audited
`requestLexLt_iff_rank_lt`, the rank comparison is equivalent to
the manuscript's exact request comparison.

The resulting order on the countable birth-labelled carrier is obtained
from the existing ranked order using these newly constructed canonical
ranks. The resulting strict order is irreﬂexive, transitive and total
on distinct vertices and agrees with the chosen fresh ordinal in each
block.

## Hostile checks

1. **No arbitrary total order:** `stageCanonicalRank` takes its rank
   from predecessor counts in the exact finite lexicographic order.
   Distinct dependent request records have different ranks by #232/#233.
2. **No circular order construction:** The order of `U_(n+1)` is
   defined using only the existing order of `U_n`, its current finite
   graph, and the finite catalogue. No order on `U_(n+1)` is used to
   compute its own request ranks.
3. **No renaming of old vertices:** The successor carrier is a literal
   `Sum`; the old summand is ordered by its inherited order, all its
   members preceding fresh vertices.
4. **Dependent vertices:** A fresh vertex consists of a request and
   `Fin (freshSize request)`. Equal ranks determine equal requests,
   then equality of ordinals determines the same `Fin` element.
5. **Empty level / zero fresh size:** An empty request catalogue yields
   an empty fresh carrier. The order construction requires no
   inhabitedness or singleton request.
6. **Block compatibility:** Both the stage successor order and
   the countable birth order compare fresh vertices with equal request
   by their literal `Fin` ordinals, not by another chosen enumeration.
7. **External dependency:** The stage ordering does not prove genericity,
   finite unique level lifting, or an embedding monoid isomorphism.
   These remain distinct obligations after canonical order verification.

## Verification contract

Check the full Lean import graph, standard axiom report and placeholder
scan on the same commit. The new theorem source must be compiled and
its four order conclusions checked before the manuscript's finite
order marker is promoted. The finite-lifting and monoid statements
remain partial even if this order bridge passes.

The seven roles are separate hostile proof checks, **not** independent
human referee certifications.
