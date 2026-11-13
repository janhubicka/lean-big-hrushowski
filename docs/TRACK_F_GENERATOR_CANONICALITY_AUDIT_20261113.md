# Track F — canonical closure condition is independent of SCC generator
13 November 2026

This branch is based directly on Track F #270 (after merged #497).
It does not depend on the new fixed-old-order bijection branches and
makes no change to the manuscript or its validation markers.

## Statement

For x and y in the same strongly connected component of a finite
orientation, the actual successor closures coincide as finite
subsets of the original vertex set:

\[
 C_x=C_y,\qquad P_x=P_y.
\]

They therefore carry exactly the same induced directed orientation,
the same restricted vertex enumeration and the same family of
complete adjacency-code minimizers. In particular, canonicality
of the current global order can be tested at any vertex of the SCC.

The module \`N0GeneratorCanonicality.lean\` proves
\`canonicalClosureMembership_iff_of_component_eq\`,
\`isCanonicalAtComponent_iff_generator\`, and the resulting
\`mem_canonicalNextComponentChoices_iff_generator\`.

This replaces an unnecessary quantification over all generators
of B by a single check at the actual chosen generator of B.
The difference is only presentation and proof reuse; the set of
permitted next internal B orders is unchanged.

## Seven internal adversarial referee checks

1. **Full closure.** The equality must concern C_x and P_x,
   not merely the induced orientation on the top SCC or
   the outgoing edge set of the chosen generator.
2. **Complete code.** The row-major directed matrix records
   all arrows and nonarrows on C_x, including pairs within P_x
   and cross pairs.
3. **Dependent carrier.** The proof must use literal equality
   of the actual finite closure sets to identify the subtype
   enumerations and their finite ordinal carriers; an
   arbitrary isomorphism is not enough.
4. **Same SCC only.** For different SCCs, C_x and C_y can
   differ. The negative control uses the two vertices
   of a directed edge, whose successor closures differ.
5. **Actual generator.** The chosen generator of B belongs
   to B. Its membership must be proved, not postulated.
6. **Quantifier.** The equality of the canonical test for
   each vertex implies the universally quantified
   \`IsCanonicalAtComponent\` condition, not merely
   the converse implication.
7. **Certification.** Dedicated exact-head Lean build,
   standard-axiom audit, placeholder scan and independent
   exhaustive finite regressions must pass. The panel is
   an internal role-separated audit, not external peer review.

The independent regression exhausts 653 finite orientations on
at most four vertices, all global labelled orders, and every
pair of generators in the same SCC. It checks the exact closure
and lower-part sets and equality of their minimum-code tests.

## Next application

Once the fixed-old closure bijection PR #510 passes, the present
generator reduction allows us to identify the concrete
\`canonicalNextComponentChoices\` set of #497 with the preimage
of the canonical complete-code minimum class on C_B, evaluated
at the single generator. The local code fibre has exactly g_A(B)
members. The resulting theorem will establish the uniform
next-component fibre count, subject to kernel certification.

The conditional finite global product theorem from merged #488
and the reachable-history induction from merged #482 then
complete the finite counting part once their histories are
identified with successive component choices. The infinite
N₀ big Ramsey theorem remains separate.
