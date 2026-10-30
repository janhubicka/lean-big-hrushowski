# Adversarial audit: complete C_F code under a partial old-source map

30 October 2026

## Claim

The target request constructed from a map defined only on the
selected old source S has the same complete ordered adjacency
matrix as the source request. Its literal support is Q=e[P]
and the relabelling of the local graph is an induced bijection
on the old support that fixes the fresh Fin ordinals.

The proof uses the existing generic namedBaseGraph_orderedAdjacencyCode,
avoiding a second proof of preservation of the row-major adjacency
matrix. No extension of e:S→V to a total map U→V is introduced.

## Hostile checks

1. **Empty-target.** If S and V are empty, the old map e is the
   empty function. The statement must remain well-typed even
   when U is nonempty. All support coordinates are absent and
   the complete code consists solely of fresh-fresh data.

2. **Graph.** Full induced adjacency is preserved by the
   named-base relabelling on the entire support-plus-fresh
   graph. The matrix includes old-old, old-fresh and
   fresh-fresh bits, including every nonedge.

3. **Order.** The support relabelling is the unique increasing
   order isomorphism inherited from e on P. An arbitrary
   support permutation might preserve graph isomorphism
   while changing the ordered code; it is not used.

4. **Finite types.** The source and target fresh intervals
   have exactly the same natural-number size by the
   target request construction. No cast to a different
   ordinal interval or arbitrary finite enumeration
   is introduced.

5. **Scope and kernel.** The theorem does not establish the
   target support's d-closedness; that remains a stated
   hypothesis of the request constructor. It does not
   yet compare two different request codes under the
   partial source map, prove simultaneous inducedness,
   or finish finite unique level lifting.
   Full CI, standard axioms and placeholder audits are
   required before verification.

These are distinct adversarial mathematical checks within
the project, not independent external human referee reports.
