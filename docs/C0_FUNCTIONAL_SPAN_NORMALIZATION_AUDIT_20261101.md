# Track A — adversarial review of arbitrary functional-span normalization

Date: 1 November 2026. Source:
`BigHrushovski/C0FunctionalSpanNormalization.lean`.

This is a role-separated internal mathematical review, not
independent human or external-agent refereeing.

## Exact claim

Let `G` on finite `A` and `H` on finite `B` carry minimal-strong
component presentations `κ_A, κ_B`. Let a common graph `P`
embed by arbitrary injections `i:P→A` and `j:P→B`.
The two graph structures agree on the named base, and their
**complete canonical unary values** agree there as the literal
images of one named function `F:P→Finset P`:
`C_G(i p)=i[F(p)]` and `C_H(j p)=j[F(p)]`.

Under the finite 2-sparsity hypotheses, the verified split
equivalences `A ≃ P ⊕ Tail(i)`, `B ≃ P ⊕ Tail(j)` put
the complete data into exactly the tagged form required by
`TaggedAmalgam.exists_taggedFunctionalAmalgam_of_named_base`.

The result is one explicit finite graph on
`P ⊕ (Tail i ⊕ Tail j)` with an actual component index
whose steps are empty or minimal strong; its two graph factor
maps are induced and strong, and every complete unary value of
each factor transports **exactly** to the whole named target
value. The two embeddings may have different original
component chronologies on `P`.

This is the first arbitrary finite base-labelled functional
amalgamation bridge required by the finite request scheduler.
It is not a countable extension theorem.

## Adversarial referee 1 — literal base labels

The injected old base is split by the equivalences
`splitEquiv i hi` and `splitEquiv j hj`. The new lemma
`splitEquiv_symm_base` proves that the inverse equivalence
sends the actual named point `i(p)` **exactly** to `inl p`.
No arbitrary isomorphic base copy or permutation of base labels
may replace this equality. The point is crucial for later
requests that prescribe their old vertices pointwise.

## Adversarial referee 2 — complete unary values

Transport is via
`FiniteC0.canonicalValue_relabel`, which preserves all
backward-reachable whole components and their vertex fibres,
not just adjacency or a one-step predecessor set. The identity

`image(e, image(i, F(p))) = image(inl, F(p))`

uses the literal identity `e(i(p))=inl(p)`. Thus the tagged
lemma's named-base closure assumptions are *derived* from the
original factor data. The wished-for preservation in the final
amalgam is not an input premise.

## Adversarial referee 3 — minimal stages

`FiniteC0.minimalSteps_relabel` transports every original
empty-or-minimal strong stage across the split equivalence.
No step may acquire an extra vertex by changing labels.
The certified tagged theorem then frontloads the right closed
base, retains the entire first chronology, and appends the right
tail. This avoids aligning incomparable base component orders.

## Adversarial referee 4 — graph inducedness

The normal forms are graph pullbacks under equivalences,
so both positive edges and *absent* edges are reflected.
The conclusion invokes `TaggedAmalgam.freeGraph_left/right`
and composes the biconditionals with the split maps.
Predimension and 2-sparsity transport through the same
induced maps; positive-edge homomorphisms alone would not work.

## Adversarial referee 5 — empty and noninitial bases

The construction must also handle `P=∅`, one empty private
tail, and a common closed base whose original components
were not initial. No total order on the common base is
required, nor any surjectivity of the original index.

An independent Python implementation checked **729,686**
exact complete-value transports on all graphs of order at most
four and the indicated indexed relabellings, covering
**196,810** closed-base cases and **31,188** instances in
which the closed base was not initially placed. It found no
discrepancy. The regression belongs to
`scripts/check_c0_functional_span_normalization.py`;
it is diagnostic evidence, not Lean certification.

## Adversarial referee 6 — source/target finite languages

The finite functional diagram catalogue admits only graph
embeddings preserving the full canonical set-valued unary
values. The arbitrary span lemma likewise assumes the two
factor *complete named values* agree over P. It does not
infer this from an induced graph embedding of P alone.
This keeps the functional amalgamation class genuinely
distinct from the larger graph age.

## Adversarial referee 7 — remaining countable step

This normalized finite theorem must next be applied to every
finite request from `FunctionalC0RequestCatalogue`, including
the **given** source embedding into the current finite stage.
One must build the finite responding structure, relabel the
tagged union onto an extended initial segment of ℕ while fixing
the old labels, and preserve the complete old and new
unary values. The current graph-only fair recursion does not
do the latter.

The countable functional limit and its Fraïssé extension
property are therefore still open, and the manuscript
`prop:C0-free-generic` must remain marked partial.

## Certification gate

The exact build, `CheckC0FunctionalSpan.lean` axiom audit
and no-placeholder scan are in the dedicated
`track-a-span-normalization.yml` workflow. Its result must
pass before this proposed theorem is called verified or
merged. Keep this PR stacked on the finite request
catalogue, with no change to shared umbrella and axiom files.


## New exact finite labelled-response endpoint

`C0FunctionalFiniteResponse.lean` instantiates the arbitrary-span
normalization theorem for a current finite stage
`S : FiniteFunctionalC0 a p`, a finite request
`D : FunctionalC0Diagram b q c r`, and a **prescribed**
functional embedding `e : Fin b → Fin a`. The hypotheses state
injectivity of `e`, inducedness of its graph map and exact
preservation of all complete source unary values.

The result constructs the literal tagged free graph, a canonical
minimal-component presentation on its whole carrier, two induced
strong graph embeddings with both complete unary operations
transported, and, crucially, the equality
`leftTag(eS(e(x))) = rightTag(eD(D.embedding(x)))`
for every original source vertex `x`. The old source map is never
replaced by a chosen isomorphic copy.

**Referee 8 — redundant sparsity assumption.** The catalogue's
finite minimal-component presentations already start from the
empty graph. The new `FiniteFunctionalC0.sparse` proves
2-sparsity from this sequence via the strongness of the empty
closed set. No separate sparseness field is needed in
`FiniteFunctionalC0`.

**Referee 9 — source versus target closure.** Both
`S.unaryValue (e x) = image(e,D.source.unaryValue(x))`
and `D.target.unaryValue(D.embedding x) =
image(D.embedding,D.source.unaryValue(x))` are used. Merely
assuming graph inducedness would not provide the named-base
compatibility needed for the tagged amalgam, and the theorem
does not infer that compatibility from the graph.

**Referee 10 — labelled response property.** The old stage map
and the requested target map are induced embeddings, and both
carry complete function-value equalities. The calculation
on the shared base uses the split equivalence's literal
`symm_base` theorem. An arbitrary normal form lacking this
pointwise identity would not answer the scheduled request.

**Referee 11 — remaining embedding into a Nat stage.** The
finite tagged graph has a valid canonical presentation but its
carrier is a finite nested sum, not the required labelled
`Fin n` or a consecutive natural interval. The next step
must extend the old labels bijectively to the whole new
carrier, transport its complete function values and prove
coherence with later stage embeddings. This is not supplied
by the graph-only label transport.

The exact checker now audits
`FiniteFunctionalC0.sparse` and
`exists_taggedResponse_to_functionalC0Request` alongside
the three span normalization endpoints. The dedicated
workflow builds `C0FunctionalFiniteResponse`, rather than
only its predecessor module. No finite or countable
green claim is made before this exact run passes.
