# Track A — adversarial audit: strict growth of finite canonical functional stages

Date: 1 November 2026. The adversarial referee roles below are
internal mathematical checks, not independent human or external agents.

## Exact statement

For every finite canonical presentation
`S : FiniteFunctionalC0 n k`, construct a finite
`T : FiniteFunctionalC0 m t` with **m > n**,
an injective induced strong graph map `f: Fin n→Fin m`
fixing old numerical coordinates `(f x).val=x.val`,
and exact equality
`T.unaryValue(f x)=f[S.unaryValue(x)]`
for every old vertex. This is a strictly growing finite
functional extension even if no external request is applicable.

## Referee 1 — genuine fresh point

The finite graph growth lemma `FiniteSpan.exists_fresh_strong_extension`
provides a concrete `fresh` not in the image of the original
graph. The proof must not infer strict growth merely from
the *possibility* of adding a vertex. After transferring to a
finite ordinal, if `m≤n`, the new point's numerical label is
an old coordinate. Because every old coordinate is fixed,
the new point is then in the old image, contradicting the
certified freshness. Hence `m>n`.

## Referee 2 — full function values

The graph-growth lemma is not a functional theorem. It produces
an induced strong old graph embedding, and
`FiniteC0.exists_canonical_extension_over_embedding` is needed
to give the enlarged finite graph a canonical component index
and ensure full backward-reachable unary values on the old
factor remain exactly unchanged.

The final consecutive relabelling uses
`exists_initialSegment_canonicalFunctionalExtension`,
which preserves *all* complete unary values; it must not
silently replace the canonical finite closure by an
old-neighbour approximation.

## Referee 3 — label coherence

The canonical equivalence
`FiniteSpan.canonicalFinNumbering n` fixes every old
coordinate. The old-fixed extension equivalence is used
to label the enlarged carrier. A random finite enumeration
could permute old coordinates, ruining a future fair
countable recursion.

## Referee 4 — strongness

The old graph is strong in the intermediate fresh graph by
the existing predimension lemma, not by the extension's
eventual countable genericity. `GraphOn.strong_image_iff`
transports this assertion to the relabelled finite ordinal,
reflecting adjacency and nonadjacency along a bijection.

## Referee 5 — no circularity

The only finite input is a canonical minimal-component
presentation `S`. Its 2-sparsity is already derived
from its minimal stages by `FiniteFunctionalC0.sparse`.
No functional Fraïssé limit or strong graph generic
is assumed as a hypothesis.

## Referee 6 — remaining countable construction

This is a strictly growing **one-step** finite functional
response with no scheduled target. The eventual finite
successor must combine it with
`exists_finiteOrdinalFunctionalResponse` for applicable
functional requests, or use it as a growth-only fallback.
Then construct coherent Nat-labelled stages, verify the
complete unary operations under all later embeddings,
and prove fairness and exhaustiveness. Without this
last recursion no unconditional countable C₀ theorem
has been verified.

## CI certification

The branch must pass the exact
`C0FunctionalForcedGrowth.lean` kernel build,
`CheckC0FunctionalGrowth.lean` theorem-axiom audit,
and source placeholder scan, using the independent
`track-a-functional-growth.yml` workflow.
Keep the manuscript's countable marker partial until the
full countable construction is certified.
