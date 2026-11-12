# Track F — initial lower parts and absolute old positions (12 November 2026)

Base: Track F integration PR #270. No manuscript or
validation-marker changes.

## Finite order lemma

Let e and f be bijective enumerations of the same finite labelled
vertex set V. Suppose P is an initial segment in both and every
pairwise comparison of elements of P is the same in e and f.
Then

\[
   e^{-1}(u)=f^{-1}(u) \quad \text{for all }u\in P.
\]

Equivalently the enumerations agree at every absolute position
occupied by P. The converse (fixed old positions imply the same
old order) was already certified.

The new module \`N0InitialLowerPositions.lean\` proves the
predecessor-count formula

\[
   e^{-1}(u)
   =|\{v\in V : v<_{e}u\}|.
\]

The finite ordinal prefix is represented by \`Finset.range\`
and \`Finset.attachFin\`, then mapped bijectively to the
predecessor set. For u in the initial segment P, every
predecessor is also in P. Equality of old-old comparisons
therefore gives equality of the predecessor sets and their
cardinalities, hence equality of old positions.

## Seven adversarial referee roles

1. **Initiality referee.** Without P being an initial segment
   in both orders, the implication fails: a singleton P has
   the same internal order under any enumeration, but may
   move to another absolute position.
2. **Cardinality referee.** The predecessor count is the
   number of all earlier labelled vertices, not the number
   of edges entering u or the cardinality of a graph closure.
3. **Finite ordinal referee.** The identification of the
   rank with predecessor count uses a genuine complete
   enumeration \`Fin n ≃ V\`, not an arbitrary injection
   with gaps.
4. **Order referee.** The hypothesis is equality of *all*
   comparisons on P, including nonadjacent pairs; graph
   adjacency alone is not sufficient.
5. **Proof-irrelevance referee.** Vertex membership proofs
   in a subtype must not become extra labels or positions.
   The predecessor subsets consist of the original vertices.
6. **Application referee.** In the actual N₀ recursion,
   P_B is initial only inside C_B. No claim is made that
   P_B is an initial segment of the whole graph.
7. **Certification referee.** The exact named Lean axiom
   checks, placeholder scan and independent finite
   enumeration must pass before certification; internal
   role checks do not constitute external human refereeing.

## Independent finite regression

The script exhaustively checks every permutation of up to five
labels, each possible subset P and all pairs of permutations
in which P occurs first. It verifies that equality of old-old
comparison relations is equivalent to equality of old absolute
positions. It also verifies the predecessor-card identity
and the non-initial singleton counterexample.

## Relation to the remaining finite product formula

For a legal SCC ranking r and a fixed choice of orders on
previous components, modifying the internal order of B
does not change the comparisons within P_B, since P_B
contains only earlier SCCs. Both induced complete enumerations
on C_B list P_B first. This new lemma will therefore show
that the induced enumerations fix exactly the same old
positions, permitting a comparison with the canonical
minimum-code fibre of cardinality g_A(B).

The other remaining ingredient is to show that every
canonical full enumeration of C_B over that fixed old order
is realized uniquely by some choice of the internal order
on the top component B. The top-order restriction lemma
in merged #473 supplies injectivity; the actual assembly
lemmas supply the reconstruction mechanism. The uniform
next-component fibre count is not asserted here.
