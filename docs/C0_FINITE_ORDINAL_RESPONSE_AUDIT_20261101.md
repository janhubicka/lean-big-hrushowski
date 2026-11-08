# Track A: adversarial audit of exact finite ordinal functional response

Date: 1 November 2026. This is an internal role-separated mathematical
audit, not the report of independent human or external-agent referees.

## Exact construction

Starting with a finite canonical stage
`S : FiniteFunctionalC0 a p`, a functional diagram
`D : FunctionalC0Diagram b q c r`, and a **prescribed** finite
functional embedding `e : Fin b → Fin a`, first use the actual
tagged finite functional response certified on stacked PR #287.

The tagged carrier `W` contains two induced strong images, the
old stage and the finite diagram target, meeting exactly on the named
source. Its component index `κ` gives all nonempty minimal strong
increments and the complete set-valued unary closures, including all
backward-reachable components.

Use the already verified `FiniteSpan.extendInitialEquiv` with the
**canonical** numbering of `Fin a` to relabel `W` onto the
consecutive carrier `Fin (Fintype.card W)`. This fixes all old
numerical labels and transports the graph and entire unary operation.
The final result has a new canonical labelled finite graph `M`,
induced strong embeddings `old`, `target`, exact old and new
unary values, and pointwise equality
`old(e(x)) = target(D.embedding(x))`.

## Adversarial roles

1. **Named base.** The image of the prescribed map, not an arbitrary
   isomorphic copy, is identified in the tagged graph. The source
   equality is transported through the *same* new equivalence.

2. **Closedness.** The source map preserves full unary values
   exactly; graph inducedness alone is insufficient, even on a
   singleton source embedded as a later vertex of an edge.

3. **Old numerical labels.** A random `Fintype.equivFin W` might
   permute old vertices. The construction uses
   `canonicalFinNumbering` and `extendInitialEquiv_old` to keep
   literal old coordinates unchanged.

4. **Complete value transport.** The full unary function of
   `M` is its canonical value, not a separately chosen function.
   `canonicalValue_relabel` gives equality for each new vertex;
   old full values follow from the composition of the tagged
   equality with the relabelling equality. No fresh vertex is
   admitted to any old unary value.

5. **Both strong embeddings.** Predimension-strong images of both
   finite factors are verified *before* relabelling in the tagged
   carrier, then transported across the same induced equivalence
   using `GraphOn.strong_image_iff`. Both embedding functions are
   injective composites.

6. **All finite levels.** The output `M` retains the entire
   empty-or-minimal stage property under equivalence, with
   possibly unused component ranks. No new numerical alignment
   on incomparable base components is required.

7. **Growth obstruction.** The target may be entirely contained
   in the old stage. Therefore the theorem **does not** assert
   `size > a`. A fair countable stage construction must always
   force an additional isolated point, or otherwise prove
   unbounded stage sizes independently. Claiming exhaustiveness
   from the finite response alone would be false.

8. **Countable boundary.** The theorem only constructs one
   labelled finite ordinal response. It does not define a
   finite Nat-supported graph with exact complete unary
   values outside its stage, or show the coherency of
   infinitely many extensions. The successor construction,
   fair iteration and function-union verification remain open.

## Certification gate

The branch must pass the exact
`BigHrushovski.C0FunctionalFiniteOrdinalResponse` build,
`CheckC0FiniteOrdinal.lean` axiom audit and placeholder scan
in `track-a-functional-ordinal-response.yml`. The source is
stacked on PR #287 and must not be promoted to a validated
manuscript theorem or merged until these checks pass.
