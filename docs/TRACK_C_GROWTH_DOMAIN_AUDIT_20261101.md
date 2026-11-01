# Track C — published nonnegative growth-domain bridge

The manuscript (v52, 01_introduction, 03b_enumeration_CF) assumes a
continuous nondecreasing unbounded F on nonnegative reals into
nonnegative reals, with F(0)=0. The finite Lean extension theorem
requires a monotone unbounded F on all reals. The latter need not
be a separate hypothesis: set F_ext(x)=F(max(x,0)).

The present exact Lean subtype `NonnegativeReal = {x : ℝ // 0≤x}`
and `PublishedGrowth = NonnegativeReal → NonnegativeReal` preserve
both domain and codomain restrictions. The endpoint
`extendPublishedGrowth_agrees` proves exact agreement for every
nonnegative x; `extendPublishedGrowth_nat` specializes it to every
finite vertex cardinality. The remaining endpoints certify F(0)=0,
monotonicity, nonnegativity and unboundedness for the extension.

**Scope:** this is a numerical adapter only. To complete Track C,
instantiate `CFRealFiniteGenericity.finiteRealDClosedInterval_globalResponse`
with `extendPublishedGrowth F` and its certified hypotheses and use
the cardinality equality to transport the growth-class predicate.
The countable strict back-and-forth theorem and singleton/empty-base
requirements are separate.

## Internal adversarial panel

1. Domain referee: negative real inputs are clamped to zero. No
   unlicensed value F(x) for negative x appears.
2. Codomain referee: nonnegative output values are part of the
   `PublishedGrowth` type, not inferred from monotonicity alone.
3. Finite-class referee: exact agreement at each natural cardinality
   is required, not mere eventual agreement or a monotonic estimate.
4. Inverse referee: genuine unboundedness is preserved. The extension
   is constant only on the negative half line and therefore preserves
   every positive-domain growth threshold.
5. Certification referee: all theorem endpoints need an isolated
   Lean build and `#print axioms` check; no manuscript marker
   is promoted before CI.

Status: implementation created, CI pending. This is internal
role-separated checking, not externally recruited referees.

## Complete published finite-response specialization

`CFPublishedFiniteGenericity.lean` now states the prescribed-base
finite extension theorem with **F : PublishedGrowth** directly.
The source finite graph is tested against
`publishedCardinalGrowth F`, not against an unannounced real
extension; the two cardinal predicates coincide by the exact
`publishedCardinalGrowth_eq` theorem.

The full target result includes injection, exact pointwise fixing
of the old source, preservation and reflection of adjacency (hence
nonedges), and global strict d-closedness of the resulting image.
It is a specialization of the existing kernel-checked real-response
theorem; the new specialization itself remains pending CI.

Further audit: this theorem quantifies over finite linearly ordered
source vertex types, exactly as the existing finite response theorem
does. It does not assert a countable Fraisse-limit isomorphism,
finite unique level lifting or a non-precompact Ramsey result.
