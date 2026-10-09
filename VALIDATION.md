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


## Arbitrary graph predimension and finite-view transfer (certified)

A GraphOn structure has a symmetric irreflexive adjacency predicate and no
finiteness assumption on its full set of edges. For each finite vertex set,
the induced edge set is finite. We define predimension using this induced
edge count and prove submodularity directly. The finiteView construction
produces a FiniteGraph whose edge count and predimension agree on every
subset of the finite container.

This repairs the representation gap between the earlier FiniteGraph module
and a potentially infinite Hrushovski graph, while leaving the specific
finite strong-cover property and genericity of M0 unformalized.


## Infinite-graph transfer of the two-edge lemma (certified)

The same induced finite-view argument now transfers the finite
self-sufficiency relation and the two-old-incident-edge bound to a graph
with an arbitrary infinite edge relation. Given a strong exhaustion,
exactly two old incident edges make the one-point strong closure a
singleton extension. The full graph is no longer assumed to have finitely
many edges. The numerical identification with the manuscript's count of
old neighbours remains an explicit graph-interface obligation.


## Infinite-graph bridge: validation checkpoint

The [67-declaration Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37987197242) passed at source commit [99a62a2](https://github.com/janhubicka/lean-big-hrushowski/commit/99a62a2cb5205b2d03070eac5df9b71730b8afe0). No nonstandard theorem axioms were found, and ten Lean source files passed the placeholder check. The existing finite graph, decomposition, and triangle-component regressions passed as well.

The new graph interface covers arbitrarily infinite edge sets, with induced edges enumerated only inside finite vertex sets. It proves the finite-view equivalence of strong embeddings and the incident-edge singleton-closure conclusion. Exact equality between incident-edge count and the number of distinct old neighbours is not yet a separate Lean declaration; the concrete M0 strong cover/genericity and subsequent Ramsey statements also remain open.


## Old-neighbour bijection (verified)

This module makes explicit that, for a vertex x outside a finite old set A,
its incident unordered back edges correspond bijectively to the distinct
old vertices y adjacent to x. In particular the cardinality used by the
formal back-edge theorem equals the manuscript's d_i(x). No finiteness
assumption is imposed on the whole graph. The two-neighbour bound and
singleton-closure conclusion follow immediately from the earlier
finite-view transfer and strong-exhaustion results.

The companion independent regression `scripts/check_old_neighbours.py`
examines 84,073 configurations in the 1,100 labelled graphs on at most
five vertices, checking the correspondence and cardinality in each.

**Verified Lean commit:** [ae88e1c](https://github.com/janhubicka/lean-big-hrushowski/commit/ae88e1c25af73b0132170cf812e113ec5442ccc8), [successful GitHub Actions run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37989366352). The run compiled all modules and audited 74 declarations, accepting only Lean's standard logical axioms; 11 Lean source files passed the placeholder check. The independent regression checked 1,100 labelled simple graphs and 84,073 old-set/new-vertex configurations. The closure consequences are still conditional on the strong exhaustion; genericity of the specific M0 is not yet formalized.


## From finite strong successor steps to global strongness (verified)

StrongChain assumes only a countable family of finite stages covering the
ambient vertex type and strongness of each inclusion U_n <= U_(n+1).
The new induction proves U_n <= U_m for all n <= m, then shows every
U_n is strong in the entire ambient structure by placing each finite
test set inside a later stage. This supplies a StrongExhaustion and
FiniteStrongCover without assuming global strongness of the stages.
Thus the usual direct-limit step in the strong Fraisse construction is
formally isolated. The actual construction of the countable generic graph
and proof of its extension property remain to be formalized.

The independent finite-model regression for three-stage covering
strong chains checks every labelled graph with up to four vertices,
including 5,074 valid strong-chain configurations. The general proof
still rests on the kernel-checked arbitrary-predimension argument.

**Certified checkpoint:** [626275e](https://github.com/janhubicka/lean-big-hrushowski/commit/626275e464f20a5883b7d6fcab71553f85711ced), [passing Lean CI](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37989676436). The run compiled the full development and audited 73 declarations with only standard logical axioms, no proof placeholders, and 5,074 finite three-stage covering-chain regressions. An actual strong Fraisse construction is still required to instantiate the chain for M0.


## Free amalgamation predimension interface (verified)

In a finite no-crossing union, every induced edge belongs to one of
the factors. The predimension is consequently modular, with the
predimension of their intersection subtracted. If the common base is
strong in the other factor, each factor is strong in the union.
This records the key predimension calculation used when freely adjoining
finite extensions. It does not construct a universal free amalgam,
verify C0 sparsity for the union, or prove Fraisse genericity.

**Validated Lean code:** [e04d117](https://github.com/janhubicka/lean-big-hrushowski/commit/e04d117f8e62f31c4d4ab6cafa318c9884b56c1e), [passing 72-declaration axiom audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37990251957), with standard logical axioms and no proof placeholders. The additional
independent finite-graph regression is included in this PR and awaits the
combined final CI run before merge.


## Two-sparsity preservation in no-crossing free unions (verified)

IsTwoSparse represents the finite C0 condition: every induced subset
has nonnegative predimension. The new theorem proves that a free union
A union B is 2-sparse if A is 2-sparse and the common overlap A intersect B
is self-sufficient in B, assuming there are no edges crossing the
disjoint tails. The symmetric version is included. In addition, a
strong extension of a 2-sparse base is 2-sparse.

This checks the closure property of the class C0 in the finite
no-crossing configuration. The universal strong free-amalgam
construction, the Fraisse limit and its generic extension property
are separate obligations.

The independent exhaustive checker `scripts/check_c0_free_union_sparsity.py`
examines all labelled simple graphs on at most five vertices and tests
the entire subset-wise 2-sparsity property and both strong free-union
directions. The general theorem remains dependent on the Lean kernel
build and a standard-axiom audit.

**Certification:** the [89-declaration integrated CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37991564215) passed at commit [4a730c8](https://github.com/janhubicka/lean-big-hrushowski/commit/4a730c814d6ebd1c8e368d99237f23066c7941f6). Only the standard logical axioms occurred and 14 Lean files were checked for placeholders. The 1,100-graph regression checked 635,495 no-crossing pairs, 624,416 2-sparsity-preserving pairs in each direction, and 244,695 strong extensions. No claim is made yet that the generic Hrushovski limit has been constructed in Lean.


## Concrete graph free join of two induced pieces (certified)

New module FreeJoinConstruction.lean constructs a graph on a common
vertex carrier by retaining only edges internal to either finite piece.
When the two graph predicates agree on the common base, the resulting
induced graph on each factor and all predimensions in that factor agree
literally with the original graph. The join has no crossing edges.
This is an actual free graph construction on previously identified
vertex sets. A disjoint-copy/quotient construction for arbitrary abstract
embeddings, and then the Fraisse extension property, remain unverified.


The independent regression
`scripts/check_actual_free_join.py` constructs the join for every pair
of labelled graphs up to four vertices and every pair of vertex subsets,
checking overlap compatibility, preservation of induced factor edges,
no crossing edges, 2-sparsity and strongness in applicable cases.
The initial 1,052,741 configurations had no counterexamples. The kernel
build and axiom audit, not these computations, determine Lean verification.


## Strong finite graph free amalgamation on a common carrier (certified)

The freeJoin construction now incorporates the previously audited
no-crossing predimension lemmas: when the common base is strong in
both compatible factors, the free join is 2-sparse and the two
inclusions into the join are strong. The theorem freeJoin_strong_amalgam
states these three conclusions simultaneously. The construction is
still on an already common vertex carrier; arbitrary embeddings must
be transported onto a common carrier before applying it.


## Concrete free join: audited theorem boundary

At [commit 24e050c](https://github.com/janhubicka/lean-big-hrushowski/commit/24e050c510e4ccc47f6034899e7b8a5e2acd6054), the [passing 102-declaration CI audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37995191720) certified the actual free-join construction.
The declarations GraphOn.freeJoin_adj_left/right preserve both induced factor graphs, GraphOn.freeJoin_noCross excludes crossing edges, GraphOn.freeJoin_predim_left/right preserve induced predimension, and GraphOn.freeJoin_strong_amalgam proves that the join is 2-sparse and both pieces are strong, under compatibility and strong-base hypotheses.

An independent regression covered 1,052,741 graph/subset combinations, 894,763 compatible pairs and 893,483 strong 2-sparse joins. The graph pieces are already represented as subsets of a common carrier. To amalgamate arbitrary abstract finite structures over embeddings, a disjoint tagging and base-identification construction is still required.

The regression also has a negative control: two K5's glued along a common K3 without a strong-base hypothesis have predimension -3. This refutes any weakening of the hypothesis to plain embeddings.


## Tagged carrier for compatible finite graph extensions (certified)

TaggedAmalgam takes arbitrary graph predicates on P+L and P+R,
identifies their P-parts and embeds them into P+(L+R).
The canonical maps are injective and overlap only on P. If the
source graphs agree on P, both inclusions are induced graph embeddings
and the join has no crossing edges between the fresh L and R parts.
This is a fresh carrier for the underlying graph, not just two
subsets of an existing common carrier. The strong-embedding transfer
for finite source graphs and the Fraisse extension property remain open.

The independent regression check_tagged_amalgams.py enumerates all
5,613 small input graph pairs in canonical tagged normal form,
including 2,875 compatible bases, and checks that the two inclusions
preserve induced graphs without crossing edges. The test also checks
2,729 examples satisfying strong-amalgamation hypotheses, but the
general strongness-transfer proof on tagged carriers is still open.


**Certified:** source commit [9c4ec90](https://github.com/janhubicka/lean-big-hrushowski/commit/9c4ec90481b8125c75fd3ccb27160bd52dbf4e93) passed the [109-declaration axiom audit and tagged regression](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37996084683). Sixteen Lean files were checked for placeholders. The exhaustive tagged-normal-form checker tested 5,613 small input pairs, including 2,875 compatible graphs and 2,729 strong-base configurations. The Lean theorem proves graph-embedding and no-crossing properties; strongness of the tagged embeddings still needs a predimension-transport lemma, so the 2,729 finite computations are diagnostic only.


## Invariance of predimension under induced embeddings (pending CI)

The new module InducedEmbedding.lean handles injective maps that preserve
and reflect graph adjacency. It proves that unordered edges on the image
of any finite vertex set are precisely images of original unordered
edges, and hence that both the induced edge count and the predimension
are invariant. The ambient graphs may be infinite.
This is the numerical ingredient needed to transport strong finite
embeddings into the tagged free graph carrier.


## Strongness and 2-sparsity under induced embeddings (pending CI)

Once the finite edge and predimension identities have been proved,
every finite intermediate substructure of the image is a filtered
image of a finite intermediate source substructure. This gives
equivalence of self-sufficiency on finite intervals, and equivalence
of 2-sparsity of a finite induced graph and its image. The hypotheses
still require the map to be injective and to preserve and reflect
adjacency. These general lemmas are intended for the tagged free
amalgam inclusions.

An independent regression script checks all 76 labelled simple graphs
up to four vertices, 31,548 induced injections and exterior-edge
patterns, 497,876 predimension equalities, and 2,509,516 relative
strongness equivalences. Both injectivity and reflection of
adjacency are explicitly tested by negative controls.
