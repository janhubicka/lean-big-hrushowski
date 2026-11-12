# Track F — a direct criterion for canonical finite orders (12 November 2026)

Based on Track F #270, using the previously merged canonical local
fibre results #413. No change to the TeX manuscript, its validation
markers or the independent C0/CF tracks.

## Result submitted for Lean certification

For a finite orientation and an actual SCC B, let C_B be the complete
successor closure, and P_B the strict successor part. Fix a full
enumeration e0 of C_B, which prescribes the *positions* of the
already ordered vertices in P_B. A full enumeration e is canonical
precisely when:

1. e agrees with e0 at every position occupied by P_B; and
2. its complete directed adjacency matrix, read in row-major
   lexicographic order, is no greater than that of any other
   enumeration with the same fixed old positions.

Formally, \`mem_canonicalComponentLexClass_iff_le_all\`
identifies this direct test with membership in the earlier
\`canonicalComponentLexClass\`. The generic finite-order
lemma \`mem_minimumCodeClass_iff_le_all\` isolates the
elementary minimum calculation from the graph geometry.

The auxiliary \`canonicalComponentLexCriterion_base_independent\`
proves that changing the arbitrary enumeration outside P_B does
not change the test, provided the lower positions stay fixed.

These results simplify the *presentation*: the local permitted
order can be described directly, without introducing a
finite-set minimum operator in the paper.

## Internal adversarial referee panel

1. **Membership referee.** It is not enough for the code to be
   globally small. The candidate must first belong to the family
   of enumerations fixing the old positions.
2. **Directed-code referee.** The code includes *all* ordered
   pairs in C_B, recording nonedges as well as oriented edges.
   It is not an undirected adjacency code or an abbreviated
   edge list.
3. **Induced-closure referee.** The code is computed on the
   orientation induced by the complete C_B, not on the whole
   ambient graph. These give different answers in the
   triangle-plus-incoming-leaf example.
4. **Pointwise referee.** The lower part P_B is fixed at every
   enumerated position, not merely setwise. A sink-swap test
   detects the difference.
5. **Representative referee.** The candidate has no dependence
   on how new top-component vertices were listed in the
   initial base, beyond the stipulated P_B positions.
6. **Scope referee.** This is an equivalence of two *finite
   local* formulations. It does not prove that global permitted
   orders decompose into the claimed local choices, nor the
   product count or any Ramsey theorem.
7. **Certification referee.** Exact theorem axiom printout,
   scan for placeholders and independent exhaustive finite
   tests are required at the PR's head. Role-separated
   analysis is not external human peer review.

## Finite audit

The independent test enumerates all orientations of order
at most four, every complete induced SCC closure, every
base enumeration, and every target enumeration. The direct
quantified criterion is compared with the actual minimum-code
class. Negative checks include wrong lower positions and
a strictly nonminimal code. The existing independent local
fibre regression checks the factor g_A(B).

## Next step

The open global proof is to show that for every legal component
ranking, choosing successive component orders by this local
criterion yields exactly the globally permitted enumerations
and has uniform fibre cardinalities g_A(B). A general
dependent-history product lemma is already available.
