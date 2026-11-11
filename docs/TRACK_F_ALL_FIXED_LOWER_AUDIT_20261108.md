# Track F — every fixed-lower enumeration, minimum complete code (8 November 2026)

**Scope.** This PR is stacked on the pending finite minimum-code PR #377,
which in turn is based on the Track F orientation integration PR #270.
Neither paper TeX nor its validation markers are changed. No infinite
big Ramsey assertion is certified.

The previous conditional theorem \`minimumCodeClass_card\` requires
(i) pairwise agreement at positions occupied by a fixed old part P,
(ii) stability of the family under all complete-code-equivalent
pointwise-P automorphisms, and (iii) completeness of the code.

The new theorem chooses the *concrete full family* of bijections
\`Fin n ≃ C\` that agree with a fixed enumeration at each position occupied
by P. The first two requirements become proven facts. In particular,
bijectivity implies that a position not originally occupied by P
cannot acquire an element of P; hence this agreement is symmetric and
transitive. The code is the full directed Bool matrix (including
nonedges), injected into a finite ordinal by a chosen equivalence.
The minimum-code class now has precisely \`|Aut(C)_(P)|\` elements.
The chosen indexing order of all matrices is **not asserted to be lex**;
the cardinality is invariant under the choice of code order.

## Independent adversarial referee roles

1. **Old-position referee:** check that symmetry uses injectivity,
   and that the statement fixes P *pointwise*, not just setwise.
   A two-element edgeless orientation exposes the latter error.
2. **Orbit referee:** check stability under every pointwise stabilizer,
   not only under one selected automorphism. A singleton choice set
   fails when the stabilizer has order two.
3. **Matrix referee:** code equality must characterize the entire
   directed adjacency relation; constant codes fail for a single edge.
4. **Empty-set referee:** the empty graph and P=empty must be covered;
   the chosen enumeration ensures the finite family is nonempty.
5. **Order-referee:** distinguish the numerical order on matrix indices
   from the lexicographic convention of the manuscript. This PR proves
   a cardinality only, *not* identification of preferred canonical
   orders as printed.
6. **Integration referee:** this is a local family over C. To obtain
   the finite N0 formula, still prove (a) every admissible component
   order induces the appropriate full local family on C_B with P_B
   already fixed, (b) reconstruct global component-interval orders
   bijectively from all component choices, (c) instantiate the
   dependent-choice count. Infinite recurrence and degree-one Ramsey
   still require separate proofs.

**Certification:** exact named endpoints in
\`CheckTrackFAllFixedLowerAxioms.lean\`, placeholder audit and an
independent finite test covering all 2-orientations of up to four
vertices, all old subsets, two base orders, plus selected five-vertex
cases. Finite tests do not replace Lean kernel/axiom verification.
Keep draft until both the isolated and full exact-head workflows pass.
