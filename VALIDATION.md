# Validation ledger — 9 October 2026

Manuscript: The-big-Hrushovski (v52). First milestone: finite predimensions.

| Manuscript statement | Lean declaration | Status |
| --- | --- | --- |
| Definition of graph predimension and submodularity (Sections 1–2) | BigHrushovski.FiniteGraph.predim_submodular | Verified — [7-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37976439415) |
| Intersection of finite strong substructures (Lemma intersection, first assertion) | BigHrushovski.Predimension.strong_inter | Verified — [7-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37976439415) |
| Transitivity of finite strong substructures | BigHrushovski.Predimension.strong_trans | Verified — [7-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37976439415) |
| Strict d-closure implies self-sufficiency | BigHrushovski.Predimension.strong_of_dClosed | Verified — [7-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37976439415) |
| Intersection of finite d-closed substructures | BigHrushovski.Predimension.dclosed_inter | Verified — [10-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977234148) |
| Transitivity of finite d-closed substructures | BigHrushovski.Predimension.dclosed_trans | Verified — [10-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977234148) |
| Least strong hull within a fixed finite ambient graph | BigHrushovski.Predimension.exists_least_strong_hull | Verified — [15-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977945496) |
| Existence of a finite strong container in the countable M_0, and global hull | None | Open (requires strong Fraisse chain and finite-character transfer) |
| Equality with model-theoretic algebraic closure | None | Open |
| Enumeration, lifting, Ramsey and Ellentuck theorems | None | Open |

Only the finite-set statements listed here are formalized. The first assertion
of the intersection lemma is stronger than needed, because the general abstract
predimension theorem is instantiated by the *proved* submodularity of graph δ.

Audited Lean commit: [1a4dfafc](https://github.com/janhubicka/lean-big-hrushowski/commit/1a4dfafc983305b28f0489ee727d62dd8f2315fa).
The [successful GitHub Actions run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37976439415) built all modules and checked seven declarations, with only Lean's standard logical axioms and no placeholders.

Green marks require a successful build, exact theorem match, and axiom audit
of a pinned commit. Orange indicates partial coverage; blue is an interface
marker. A build still pending cannot be called machine verified.

Adversarial review perspectives:
1. Predimension: check each unordered edge counted once and direction of inequality.
2. Closure: distinguish strong-in-finite-C from strong-in-M, and finite hull existence.
3. Ramsey: never promote the finite predicate lemmas to recurrence or exact big degrees.
4. Lean: inspect elaborated theorem types, axioms, and forbidden placeholders.

These are separate hostile checking perspectives, not human referee certification.

## Second finite theorem layer (certified)

The strict relation used in C_F is now treated separately from self-sufficiency.
The new targets `Predimension.dclosed_inter` and `Predimension.dclosed_trans` are proved and audited.
Both need the **strict** inequality on every proper extension: converting
the goal to the non-strict IsStrong predicate would be an invalid repair.

The independent bit-set checker enumerates all 1,100 labelled simple graphs
on at most five vertices, including tests where graph edges cross a union.
These checks are diagnostic only; the [successful CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977234148) builds the formal proofs and audits all 10 Lean declarations. The corresponding [audited commit](https://github.com/janhubicka/lean-big-hrushowski/commit/9bd2d4238ac92dbf18533f05a8479e447ebeacb5) contains no proof placeholders and passes all finite-model checks (1,065,509 submodularity instances, 1,753,601 d-closed intersections, 686,097 transitivity cases).


## Third finite theorem layer (certified)

The finite-hull construction takes the intersection of all strong subsets of
the *same fixed finite ambient set* that contain a prescribed source. The
intersection-family induction and the leastness property are audited in Lean
as Predimension.strong_intersectFamily and
Predimension.exists_least_strong_hull. The [successful 15-declaration
audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977945496)
at [0b880c93](https://github.com/janhubicka/lean-big-hrushowski/commit/0b880c93bc7125cd80f0d340f041137d4be3a52b)
also passed the 1,100-graph model checker.

This finishes the **finite-ambient** portion of Lemma intersection.
The remaining countable statement requires showing every finite source
in M_0 lies in a finite strong container and comparing the resulting
hulls between containers. The current Lean development does not formalize
the generic strong Fraisse limit.


## Fourth layer: global closure from a supplied strong exhaustion

Module GlobalClosure.lean defines finite globally strong substructures in an
ambient (possibly infinite) vertex type. It formalizes:
- their closure under intersections;
- independence of finite strong hulls from globally strong containers;
- an increasing strong exhaustion as explicit hypothesis data;
- finite generated closure, monotonicity, idempotence, and exactness on
  finite globally strong substructures.

Pending CI and statement audit. This formalization is **conditional on the
strong exhaustion**. Its existence for the actual countable Fraisse limit,
and the graph/partial-function representations, remain to be formalized.

A corrected two-edge path example in ADVERSARIAL_REVIEW.md uses the endpoints
A={0,2}; A={1,2} would not have the asserted predimension.


## Fifth layer: minimal closure increments (pending CI)

The manuscript's lemma equalclosure reduces to the precise
IsMinimalChoice hypothesis over a finite globally strong requirement.
The new module MinimalExtensions.lean formalizes the equality of
relative closures and the absence of an intermediate strong substructure.
Existence of a minimising choice in each nonempty finite requirement
is a separate obligation, as is scheduling all requirements to exhaust M_0.


## Finite minimizer selection (pending CI)

The next increment can be selected rather than merely assumed. Among the
finite nonempty candidate set D minus A, select a vertex whose generated
closure has minimum cardinality. Any proper subset closure would have
smaller cardinality, so the vertex satisfies IsMinimalChoice. The resulting
finite extension has no intermediate strong substructure. This proves
the one-step minimalisation claim, conditional on the globally strong
exhaustion and the given finite strong requirement.


## Sixth layer: finite minimal decomposition (pending CI)

A finite globally strong extension is refined by strong induction on
the number of vertices still outside the prefix. Each step selects a
minimum-cardinality one-generated strong closure. This closure is a
minimal strong extension and strictly increases the prefix, so the
finite construction terminates at the prescribed strong container.

The chain is encoded by an inductive relation rather than by imposing an
arbitrary numerical length. A complete exhausting enumeration of the
countable Hrushovski limit remains a distinct scheduling argument.


## Exact manuscript interface for the finite decomposition

The theorem finite_minimal_decomposition_of_strong takes a finite strong
extension A <= D with D globally strong and returns a finite chain of
minimal strong extensions from A to D. This directly matches the finite
refinement used in the closure-component construction, conditional on the
strong exhaustion and on the existence of the ambient strong embedding.

The independent finite-model regression tests all labelled simple graphs
with at most five vertices, checking minimiser selection, equality of
relative closures, absence of intermediate strong substructures, and
strict progress. These checks do not replace the Lean proof.
