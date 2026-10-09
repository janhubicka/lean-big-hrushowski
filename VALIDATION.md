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
| Strong hull independent of finite globally strong container | BigHrushovski.Predimension.strongHull_eq_of_global | Verified — [35-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886) |
| Finite closure under a supplied strong exhaustion | BigHrushovski.Predimension.StrongExhaustion.closure_eq_strongHull | Verified — [35-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886) |
| Existence of an inclusion-minimal one-generated closure | BigHrushovski.Predimension.StrongExhaustion.exists_minimal_choice | Verified — [35-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886) |
| Finite minimal strong extension decomposition | BigHrushovski.Predimension.StrongExhaustion.finite_minimal_decomposition_of_strong | Verified — [35-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886) |
| Existence of a finite strong exhaustion for the actual countable M_0 | None | Open (requires explicit Fraisse limit construction) |
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


## Fourth layer: global closure from a supplied strong exhaustion (certified)

Module GlobalClosure.lean defines finite globally strong substructures in an
ambient (possibly infinite) vertex type. It formalizes:
- their closure under intersections;
- independence of finite strong hulls from globally strong containers;
- an increasing strong exhaustion as explicit hypothesis data;
- finite generated closure, monotonicity, idempotence, and exactness on
  finite globally strong substructures.

The [35-declaration CI audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886) verifies these statements. This formalization is **conditional on the
strong exhaustion**. Its existence for the actual countable Fraisse limit,
and the graph/partial-function representations, remain to be formalized.

A corrected two-edge path example in ADVERSARIAL_REVIEW.md uses the endpoints
A={0,2}; A={1,2} would not have the asserted predimension.


## Fifth layer: minimal closure increments (certified)

The manuscript's lemma equalclosure reduces to the precise
IsMinimalChoice hypothesis over a finite globally strong requirement.
The new module MinimalExtensions.lean formalizes the equality of
relative closures and the absence of an intermediate strong substructure.
Existence of a minimising choice in each nonempty finite requirement is
proved by the following finite-minimiser lemma. Scheduling all requirements
to exhaust M_0 remains a separate obligation.


## Finite minimizer selection (certified)

The next increment can be selected rather than merely assumed. Among the
finite nonempty candidate set D minus A, select a vertex whose generated
closure has minimum cardinality. Any proper subset closure would have
smaller cardinality, so the vertex satisfies IsMinimalChoice. The resulting
finite extension has no intermediate strong substructure. This proves
the one-step minimalisation claim, conditional on the globally strong
exhaustion and the given finite strong requirement.


## Sixth layer: finite minimal decomposition (certified)

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


## Latest validation checkpoint

Commit [64cf4a8](https://github.com/janhubicka/lean-big-hrushowski/commit/64cf4a802bb4b224a63d0150efec1b476e6f2c69)
passed [GitHub Actions](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37984098886).
The build and the standard-axiom/placeholder checks passed for 35 audited
declarations. The finite graph regression examined all 1,100 labelled
graphs on at most five vertices. The separate decomposition checker tested
189,941 globally strong source/container pairs, 310,904 minimal
extension steps, 312,998 relative-closure identities and 621,808
intermediate-strongness cases, with no counterexample.

The **formal status** is still conditional on the supplied strong
exhaustion. The actual strong Fraisse limit, the countable scheduling
argument, the equality with algebraic closure, the later functional
presentations, and Ramsey/Ellentuck theorems are not yet verified in Lean.


## New milestone: finite strong cover gives an exhaustion (verified)

FiniteStrongCover specifies that every finite set lies in some finite
globally strong substructure. With an explicit surjective enumeration
of the ambient vertex type, CountableStrongCover constructs an increasing
finite strong exhaustion by successively closing the next enumerated vertex.
It also proves equality between closure defined from an arbitrary chosen
finite strong container and closure computed from the resulting exhaustion.
Unlike the previous module, a strong exhaustion is no longer an assumption.

The remaining instance-specific theorem must verify the finite strong cover
property for the actual Fraisse limit M0, not just give it a name.


The [47-declaration passing CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37985370062) validates the countable exhaustion construction and container-independence. The reciprocal implication is now certified as well: an existing strong exhaustion witnesses the finite strong-cover property. Hence the two conditions are equivalent when the ambient vertex type has a surjective enumeration by natural numbers.

The [49-declaration CI audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37985617994) passed at [cc4c968](https://github.com/janhubicka/lean-big-hrushowski/commit/cc4c968ff89ac13882d147aab20d05e2bf23f4e6), with only standard logical axioms and no placeholders. The concrete Hrushovski limit remains unformalized.


## Graph back-edge bound (verified)

Formalization of Proposition twoedges. The induced graph's unordered-edge
count is split into edges inside the old set and those incident to the
fresh vertex, giving delta(A+x)=delta(A)+2-d_A(x).
Self-sufficiency implies d_A(x)<=2; equality forces A+x to be strong,
so its generated strong closure is already A+x. In a minimal closure
increment this makes the increment a singleton. The last step uses
the closure/exhaustion interface already formalized.

The [successful 42-declaration audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37985274482) at commit [956701b](https://github.com/janhubicka/lean-big-hrushowski/commit/956701be5ac9ff4c9294608706049b68acd3b92c) proves the displayed induced-edge counting lemma, the numerical bound, and closure singleton conclusion. It audits all declarations for nonstandard axioms and checks eight Lean source files for placeholders.
**Remaining interface detail:** the formal back-edge count is an unordered-edge count, while the manuscript uses the number of old neighbours. For a simple graph these coincide by the two-element-edge representation; a standalone Lean bijection lemma is not yet in this PR. Until then mark the manuscript proposition as partial rather than claiming that the formal statement contains this identification.

**Further scope limitation (adversarial check):** `FiniteGraph` stores a *finite* set of ambient edges. Thus the C0 back-edge theorem is formally a finite-edge counting statement, with a separate abstract exhaustion parameter for its closure consequence. It is not yet a literal graph-theoretic model of the infinite M0. Transport to the countable M0 requires proving compatibility of finite strong containers (or introducing a graph interface with infinitely many edges but finite induced subgraphs). The corresponding manuscript marker must remain orange until this interface is formalized.
