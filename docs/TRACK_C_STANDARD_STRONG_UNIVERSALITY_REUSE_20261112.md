# Track C — finite strong universality is an empty-base extension

**12 November 2026. Status:** candidate change, pending exact-head Lean,
standard-axiom and placeholder checks. The checks below are independent
logical referee roles conducted internally, not external human reviews.

## The refactoring

The existing `publishedBirth_finiteStrongUniversality` proof
repeated the same empty-base finite-source construction for the
actual birth graph. The new general theorem
`CFDClosedBackAndForth.finiteStrongUniversality_of_standardExtensions`
isolates that calculation:

If `G` has the ordinary prescribed strong extension property,
its empty set is globally strictly `d`-closed, and the finite
growth-class source `B` has strictly `d`-closed empty base, then
`B` has a *globally strictly `d`-closed induced copy* in `G`.
The argument takes the unique function from the empty subtype
and applies the given finite extension property with `a=∅`.

This is a finite statement: no enumeration, source order,
countable carrier, finite strong chain or free-amalgamation
assumption on the target is used. The original published theorem
retains its exact Lean statement, but now follows by direct
instantiation of this general lemma, using the already certified
actual birth extension and global empty-base theorems.
No mathematical manuscript text or markers are changed.

## Adversarial referee panel

**1. Two independent empty-base requirements.**
The source needs `IsDClosed ∅ univ`, which does **not** follow
from the numerical inequality alone. The target needs
`IsGloballyDClosed ∅`, which is not implied by its standard
finite response property. Both assumptions are explicit in the
general theorem and discharged separately for the birth graph.

**2. Original finite source.** The map is defined on the *literal*
finite source type `W`. The empty old subtype has no vertices,
so its prescribed map is uniquely defined without choosing
source labels or a linear order. The extension theorem returns
a map `g : W → V` on precisely the original source.

**3. Induced, not merely homomorphic.** The finite extension
predicate returns adjacency **iff** for all pairs in `W`, and
thus preserves nonedges. The returned function is injective.
The theorem does not assert any additional order preservation.

**4. Strict global target closure.** The complete finite image
is globally strictly `d`-closed in the entire target graph,
not merely closed in a chosen stage or weakly self-sufficient.
The required old-image condition is the equality of the image
of the *empty subtype* with the *empty finite set*, checked
by explicit finite-image membership reasoning.

**5. Empty graph boundary.** When `W` is empty, the theorem's
function exists uniquely, injectivity and adjacency are vacuous,
and the conclusion's image is exactly the globally strictly
closed empty set. No nonempty-source premise is introduced.

**6. Published-domain assumptions.** The birth instance retains
`F : ℝ≥0→ℝ≥0`, `F(0)=0`, monotonicity and unboundedness.
Its one-sided finite growth membership is used as given.
The separately assumed `EmptyDClosedInGrowthClass` supplies
strict empty closure in each source member. The birth target
uses the previously proved `realCountableGraph_empty_globalDClosed`
and `publishedBirth_hasStandardFiniteDClosedExtensions`;
it does not infer class free amalgamation from monotonicity.

**7. Logical scope.** The theorem proves the **converse** finite
age inclusion: every finite member of the growth class embeds
as an induced, globally strictly closed subgraph. The assertion
that every finite induced subgraph of the birth graph belongs
to the class remains the separate certified growth theorem.
Neither claim is a theorem about `R,H`, levels, ordered copies,
embedding monoids, Ramsey degrees or Ellentuck spaces.

**8. Regression and trust.** The old public theorem type is
left unchanged. No new `axiom`, `sorry`, `admit` or
`native_decide` is introduced. The dedicated workflow must
build the new generic module and the birth specialization,
check `#print axioms` of both endpoints plus the countable
certificate, and scan all source files for placeholders.
Full repository Lean CI on the identical head is also required.
