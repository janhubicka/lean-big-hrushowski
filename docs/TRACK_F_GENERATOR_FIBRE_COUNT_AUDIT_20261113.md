# Track F — the uniform canonical generator-fibre count (13 November 2026)

Stacked on the complete fixed-old closure bijection in PR #510.
The separate generator-invariance PR #517 identifies this single
generator test with the originally defined all-generator test.
No manuscript text or validation markers are modified.

## Exact proposed finite theorem

Fix any legal ranking r of the actual SCCs, an *arbitrary*
complete family of chosen internal SCC orders, and an actual
component B with chosen generator x. Let C=C_B and P=P_B.

The complete local fixed-old enumeration set of C based on the
current inherited C order is, by PR #510, precisely the image
of the actual labelled internal B orders under the SCC-update map.
The map is injective.

Among that fixed-old set, take those enumerations whose complete
directed adjacency matrix is lexicographically least.
They form the actual canonical local class from merged #413,
whose cardinality is

\[
 g_A(B)=|\operatorname{Aut}(A[C])_{(P)}|.
\]

Define \`canonicalNextGeneratorChoices\` to be the set of internal
B orders whose updated complete C enumeration lies in this
minimum-code class, using the prescribed old positions from the
current context.

New module \`N0StageGeneratorFibreCount.lean\` proves:
- The test with the updated complete enumeration as its own
  baseline is equivalent to the fixed-context minimum class;
  this uses the old-position preservation from PR #504.
- The entire canonical local minimum-code class equals the
  *image* of the actual admissible internal B orders under
  the SCC-update map, not merely an equinumerous surrogate.
- The resulting genuine generator-choice fibre has
  **exactly g_A(B) members**, for every legal ranking and every
  complete context, even when the other orders are not
  canonical.

This is the uniformity statement needed for the dependent
history count, but it concerns the chosen-generator version
of the local admissibility predicate. The separate generator
invariance theorem #517 must be used to identify it with
the exact previously defined next-choice set of PR #497.

## Internal adversarial referee panel

1. **Uniformity.** The theorem quantifies over *all* complete
   contexts and all legal rankings. It does not assume that
   earlier component orders were already canonical.
2. **Correct stabilizer.** The factor is the pointwise
   stabilizer of P in the *induced directed orientation on C*,
   not the automorphisms of the whole graph.
3. **Full code.** Complete row-major adjacency matrices record
   all arrows and nonarrows, not only a list of old neighbours.
4. **Actual labelled orders.** The choices are enumerations
   of the actual subtype B. The inverse of the full closure
   map is the top-order restriction, not an isomorphism
   class or a quotient by automorphisms.
5. **Old positions.** Canonicality can be compared across
   choices only because the inherited positions of each
   old P vertex remain *literally* fixed, by PR #504.
6. **Two inclusion directions.** A local minimum-code
   enumeration always arises from a top-B choice by the
   surjectivity of #510; conversely every admissible top
   choice gives a member of that same minimum class.
7. **Certification.** The named theorem axiom checks,
   placeholder scan, independent finite image equality
   regression and exact-head Lean build must all pass.
   This internal role panel is not external peer review.

The independent test exhausts all 653 orientations on at
most four vertices, every legal SCC ranking and every complete
labelled component-order context. It verifies the equality
of the *sets* of minimum-code complete closure enumerations
and the image of the admissible top choices, as well as the
exact stabilizer cardinality for each context. A cyclic
triangle rejects counting all six internal orders as
canonical when only three are code-minimizing.

## Remaining endpoints

Once this PR and generator-invariance PR #517 are certified
and integrated, the equality

\[
 |\operatorname{Next}_r(\mathbf e,B)|=g_A(B)
\]

for the *actual* next-choice set of PR #497 follows.
The established prefix-locality theorem #492 then ensures
the chosen tests depend only on reachable earlier histories.
The reachable-history product lemma #482 and actual canonical
data count #488 provide the remainder of the finite
product-formula route.

This still does not establish the infinite N₀ big Ramsey theorem,
the recurrence, or any N_F upper bound.
