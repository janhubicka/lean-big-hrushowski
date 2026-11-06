# Track A — adversarial audit of finite fair functional successors

Date: 6 November 2026. Source: `C0FunctionalFairSuccessor.lean`.
The separate referee roles below are independent mathematical checks
within this review, **not** reports by independent human agents.

## Exact finite statement

A finite stage `FiniteFunctionalNatStage` contains a canonical C₀
presentation on the consecutive ordinal `Fin n`. A scheduled request
is a finite **functional** extension diagram together with the actual
old labels `Fin b → ℕ`. The request applies only if these labels
can be realized by an induced embedding of its source into the finite
stage, preserving the **entire** one-generated unary values exactly.

The successor `t` must satisfy all of the following:

- `s.size < t.size` regardless of whether a request is applicable;
- an induced strong embedding `old` fixes every old numerical label;
- all complete unary values of old vertices agree under `old`;
- if the scheduled request applies, an induced strong target copy
  preserves its complete unary values, and the old source map is
  respected pointwise.

The proof reuses the two kernel-certified finite theorems:
`exists_growingFiniteOrdinalFunctionalResponse` and
`exists_growingCanonicalFunctionalC0Stage`.
No new amalgamation predimension argument is necessary.

## Referee 1 — the request is actually functional

`Applies` requires injectivity, an exact image of the requested
source labels, induced graph edges and nonedges, and equality
of the full finite unary value on each source vertex.
A bare induced graph embedding would be insufficient:
embedding a singleton as the later vertex of an edge can change
its complete closure.

## Referee 2 — no accidental relabelling

The finite response theorem fixes `(old x).val=x.val`. The labelled
target embedding agrees with the original prescribed source map
by equality `old (e x) = target (D.embedding x)`, hence
`(target (D.embedding x)).val = request.labels x`.
No chosen graph isomorphism is allowed to change these names.

## Referee 3 — full unary values on both images

The old and target copies preserve complete set-valued unary values
by exact image equality. Equality of predecessor sets or one-sided
inclusion would not imply closed finite substructures and would
invalidate the countable limit argument.

## Referee 4 — sparse/strong graph information

The finite response and forced-growth lemmas both carry explicit
inducedness and strong-image certificates. These are returned
as separate fields in the successor; neither strongness nor
nonedge reflection is inferred merely from function-value closure.

## Referee 5 — no frozen stage

If the scheduler has no decodable request, or the decoded
source map is inapplicable, the fallback invokes the
strict-growth theorem. If the request is applicable, the
strong functional response itself forces strict growth,
even if all target vertices were already present before adding
the final fresh component. Thus every successor grows.

## Referee 6 — schedule identity

The response field of `IsFairFunctionalSuccessor` quantifies
over all requests whose code equals the scheduled code. The
proof uses injectivity of `some` to show that any such request
equals the one actually answered. It does **not** answer arbitrary
other requests at the same step, which would be stronger than
required and is not needed by fair recurrence.

## Referee 7 — what remains unproved

This file establishes only existence of *one* finite fair successor.
To obtain a countable functional Fraïssé limit, one must:

1. choose a starting finite canonical structure and recursively
   choose a successor at every natural stage;
2. form coherent finite graph and complete unary operations on
   the shared Nat carrier using the exact old labels;
3. prove every global labelled finite functional extension request
   becomes applicable at some stage once its source is present,
   and is answered at a later scheduled step;
4. use the verified coherent graph/unary limit interface to show
   canonical finite stages and the functional extension property;
5. invoke the conditional `M₀` graph-reduct recognition theorem.

In particular, no countable genericity or functional homogeneity
is a hypothesis of `exists_fairFunctionalSuccessor`.
The countable manuscript proposition stays PARTIAL.

## Certification

A passing exact Lean build, `#print axioms` endpoint and
no-placeholder check in
`.github/workflows/track-a-fair-functional-successor.yml`
are necessary before merge. The role-separated audit above
is not a substitute for kernel checking.
