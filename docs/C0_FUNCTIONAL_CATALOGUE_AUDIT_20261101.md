# Track A — adversarial audit of the functional request catalogue

Date: 1 November 2026. Scope:
`BigHrushovski/C0FiniteFunctionalCatalogue.lean`.

The following are distinct internal adversarial checks, not independently
recruited referee agents.

## Referee on representation

A labelled finite member is the pair of an induced graph on `Fin n`
and a witnessing component index `Fin n → Fin k` with every stage
empty or minimal strong. Its named unary operation is always the
**complete** `FiniteC0.canonicalValue`. Thus the catalogue never
arbitrarily chooses a function unrelated to the graph and block order.
Unused indices are permitted, as in the verified finite amalgam.

The same finite functional object can have more than one witnessing
index. The catalogue deliberately enumerates presentations, not
isomorphism classes of function structures, so duplicates are harmless
for a fair schedule. A later construction must ensure requests are
tested by their actual functional values, rather than equality of
their witness indices.

## Referee on embedding semantics

A functional diagram has an induced graph embedding (edges *and*
nonedges) and exact equality of full unary-value images:
`target.unaryValue(f x) = image(f, source.unaryValue(x))`.
It does not demand preservation of numerical component ranks.
Complete value equality implies the image is functionally closed.

Counterexample to using induced graphs alone: take a singleton
source, and embed it as the *later* vertex of a two-vertex edge in a
minimal-component presentation where the earlier endpoint is a
singleton component. The graph map is induced but its complete
unary value in the target has two vertices, whereas the source
value has one. Thus the unary-preservation field is essential.

## Referee on finiteness and coding

For fixed `n,k,m,l`, all graphs and index maps are finite data;
embedding maps are finite data as well. The minimal-stage and
preservation certificates are propositions, hence proof irrelevant.
`Finite.of_injective` therefore gives each encoded diagram a
`Finite` instance from its finite graph/index/embedding tuple.

A dependent sum over the four natural size parameters is countable;
pairing a finite diagram with a labelled source map `Fin n → ℕ`
remains countable. The request code uses the same
`Encodable.ofCountable` and `Nat.pair` pattern already verified in
`FiniteCatalogue.fairRequest_after`.

## Referee on fairness

The scheduled code is the first coordinate of `Nat.unpair`.
For any request and threshold, use
`Nat.pair (Encodable.encode req) threshold`.
The second coordinate makes a return at or after the threshold
without assuming the request is applicable at that stage.
Every request repeats. This is independent of a response
algorithm and does not establish any infinite construction.

## Referee on the actual next step

This file does not construct a functional response to an arbitrary
embedded finite diagram. The verified finite tagged two-sided
amalgamation theorem handles the graph and complete values for a
literal common base, while the generic request has a labelled
embedding `Fin n → Fin m` and an arbitrary current finite stage.
The next exact step is to normalize the arbitrary span into the
literal tagged common-base carrier, preserving complete unary
values and both induced maps. Then the strong finite functional
amalgamation can supply an applicable finite response.

After finite responses, one must construct coherent growing
Nat stages carrying both graph adjacency and complete unary
values, and verify the fair recursion. Until then, neither a
functional Fraïssé limit nor the graph reduct recognition is
unconditional.

## Certification gate

The catalogue, including the exact fairness theorem, must compile,
pass the `#print axioms` audit (only standard logical axioms)
and the no-placeholder scan. No green marker on the countable
part of `prop:C0-free-generic` follows from this catalogue alone.
