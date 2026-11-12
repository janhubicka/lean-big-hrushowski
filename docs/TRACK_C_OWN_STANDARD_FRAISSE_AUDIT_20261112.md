# Track C — the constructed birth graph has the ordinary strong Fraïssé-limit properties

**Status:** candidate proof on draft PR #420; exact-head Lean build and
standard-axiom/placeholder audit are mandatory before certification or
merge. This note does not report external human referee reviews.

## New assertions

The first endpoint, `publishedBirth_hasStandardFiniteDClosedExtensions`,
removes the unnecessary linearly ordered source-type restriction from
`finitePublishedDClosedInterval_globalResponse`. It does *not* change the
source graph, the prescribed old embedding, or its vertices. The auxiliary
linear order is chosen only because the already certified construction of
ordered local requests was formalized using such an order.

The second endpoint,
`publishedBirth_standardStrongFraisseLimitPresentation`, packages on the
actual `PublishedBirthVertex` carrier all four defining properties of the
standard strong limit: a bijection with `Nat`, finite age, a covering
finite strict `d`-closed chain, and prescribed arbitrary-finite extensions.
It neither assumes nor constructs a comparison graph `M_F`, and it does
not call the prior `publishedBirth_iso_standardStrongFraisseLimit`
identification theorem to obtain the four properties.

## Adversarial referee panel

Each role checks a logically different possible failure mode. These are
internal role-separated adversarial checks, not independent human reports.

**R1 — Arbitrary finite source.** The API
`HasStandardFiniteDClosedExtensions` quantifies over any finite type
`W`, including an empty type, with only `Fintype W` and
`DecidableEq W`. Choosing `eFin : W ≃ Fin (card W)` and
`LinearOrder.lift'` supplies a temporary order without adding a
mathematical input to the proposition. No permanent order on `W`
or the target graph is introduced.

**R2 — Prescribed old values.** The old map is a function on the
literal subtype `{w : W // w ∈ a}`. The finite response theorem fixes
each such vertex. Composing the output with the equivalence between
`W` and its full subtype `{w : W // w ∈ univ}` changes no vertex
label, and proof irrelevance identifies the two membership proofs.
A fresh isomorphic copy of `W` would not justify this assertion.

**R3 — Inducedness and injectivity.** Both adjacency and nonadjacency
are reflected and preserved for *every* pair from `W`.
Injectivity follows from injectivity on the entire finite full subtype.
Using an edge-preserving graph homomorphism would not suffice.

**R4 — Global strict closure.** The conclusion remains
`IsGloballyDClosed` of the *complete* finite image in the *countable*
birth graph, not weak self-sufficiency or strict closure inside a
chosen finite stage. The two finite images coincide by explicit
membership equivalences, with no surjectivity assumed on the ambient
countable carrier.

**R5 — Empty and singleton boundary cases.** `W = ∅` is allowed by
the temporary linear order construction and the finite response
theorem. For the full Fraïssé presentation, the distinct singleton
request at every level follows from strict empty-base closure,
singleton class membership and the exact size bound. Mere
countability of a union would not supply an enumeration equivalence
from `Nat`.

**R6 — Growth assumptions.** The final theorem retains separate
hypotheses `F(0)=0`, monotonicity, unboundedness, finite
strict-free-join closure, strict empty base and `F(1)≤2`.
`extendPublishedGrowth` agrees with `F` at each natural
cardinality. There is no continuity assumption added by Lean;
continuity from the manuscript is not needed here. In particular
the free-join property must not be inferred from monotonicity.

**R7 — No countable-limit circularity.** The age proof uses
`realCountableGraph_genericCertificate_of_classFreeJoins`.
The chain is the concrete `birthDClosedChain`; the enumeration is
`natEquivBirth_of_requests`; and the standard finite response is
proved independently above. None calls the final comparison
`publishedBirth_iso_standardStrongFraisseLimit` to establish
its premise. The module now imports `CFStandardFraisseExtension` and
`CFPublishedFiniteGenericity` directly; it does not even import
the final comparison theorem module. Thus the proof-dependency
graph rules out circular use of the desired identification.

**R8 — Functional scope.** The output is a graph-language
strong Fraïssé presentation. It neither asserts preservation of
the auxiliary order nor the functions `R,H`. It does not prove
the finite unique level-lifting theorem, the full embedding monoid,
or any Ramsey or Ellentuck result. Promoting any such marker from
this theorem would be invalid.

**R9 — The other age inclusion.** The `age` field of
`StandardStrongFraisseLimitPresentation` asserts only that every finite
induced subgraph of the birth graph belongs to `C_F`. A converse is
needed before saying that its age is *exactly* `C_F`.
The new theorem `publishedBirth_finiteStrongUniversality` uses a
literally empty prescribed strong base, whose strict closure is supplied
both in each `C_F`-member and in the countable birth graph. It obtains
an induced *globally strictly d-closed* copy of every finite
`C_F)-member, without an ordering on that member. This discharges the
converse and is independently audited by `#print axioms`.

## Kernel verification gate

The dedicated workflow builds
`BigHrushovski.CFPublishedOwnFraissePresentation` and invokes
`#print axioms` on *all three* endpoints. The full repository Lean
workflow must also pass on the exact PR head. Any missing declaration,
unproved typeclass, kernel error, or unexpected axiom blocks merge.
The status of this document is conditional until those checks succeed.
