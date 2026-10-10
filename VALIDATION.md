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


## Invariance of predimension under induced embeddings (certified)

The new module InducedEmbedding.lean handles injective maps that preserve
and reflect graph adjacency. It proves that unordered edges on the image
of any finite vertex set are precisely images of original unordered
edges, and hence that both the induced edge count and the predimension
are invariant. The ambient graphs may be infinite.
This is the numerical ingredient needed to transport strong finite
embeddings into the tagged free graph carrier.


## Strongness and 2-sparsity under induced embeddings (certified)

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


## Induced embedding certification checkpoint

At source commit [660abf6](https://github.com/janhubicka/lean-big-hrushowski/commit/660abf6d7dab255ee1e70bb92e7ea32192f91721), the [116-declaration passing Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37997208601) proved exact edge-set and predimension transport, finite strongness equivalence, and 2-sparsity equivalence. Seventeen Lean sources contained no proof placeholders; all audited theorems depended only on standard logical axioms. The independent exhaustive regression covered 31,548 injected graph diagrams, 497,876 predimension comparisons and 2,509,516 relative-strongness tests. The actual tagged free-amalgam strongness theorem is not yet an explicitly audited corollary; that will be a separate next step.


## Tagged strong free amalgamation (verified)

TaggedStrongAmalgam.lean first identifies the left and right finite
domains of the fresh carrier P+(L+R), proves their intersection is the
common base, their union is the whole carrier, and that the tagged
graph has no cross edges. These structural interface lemmas are the
remaining prerequisites for applying the verified strong free-union
theorem to the tagged construction. Lean CI and axiom audit pending.


## Strong free amalgamation in tagged normal form (pending CI)

The new theorem TaggedAmalgam.tagged_strong_free_amalgam combines
the independently checked induced-map invariance of predimension,
tagged carrier identities, and the no-crossing free-join theorem.
For finite compatible graphs on P+L and P+R, when P is strong in both
and both factors are 2-sparse, the tagged graph P+(L+R) is 2-sparse,
the two induced inclusions are strong, and both induced factors remain
2-sparse. This is the expected finite strong-amalgamation property in
the canonical shared-base presentation. A source-specific Fraisse
extension property is not inferred. The tagged theorem has passed a Lean build and standard-axiom audit.


## Certified normal-form strong amalgamation — 10 October 2026

The [passing integrated CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38019222909) at [Lean commit 1a09943](https://github.com/janhubicka/lean-big-hrushowski/commit/1a09943e0ba5204c5b3b17881dc794d2dfe6a69a) audited 126 declarations with only standard logical axioms. The placeholder checker examined 18 Lean files. All previous finite-graph regressions passed.

The core theorem `TaggedAmalgam.tagged_strong_free_amalgam` says that for finite types P,L,R and graph predicates G on P⊕L and H on P⊕R agreeing on P, if both inputs are 2-sparse and the common base is strong in both, then the tagged amalgam P⊕(L⊕R) is 2-sparse and both canonical induced embeddings are strong. The theorem also asserts that both canonical images remain 2-sparse.

The earlier independent finite test `check_tagged_amalgams.py` checked 5,613 tagged input diagrams, including 2,875 compatible diagrams and 2,729 configurations satisfying the strong-amalgamation hypotheses. **Outstanding:** normalization of arbitrary abstract base embeddings to this shared-base form, and the countable strong Fraïssé extension construction. These statements have not yet been promoted to green.


## Arbitrary base embedding normalization (verified)

SpanNormalization constructs an equivalence P+Tail(i) ≃ A from an
injective embedding i : P → A, without identifying vertices outside
the image of i. Pulling back a graph along this equivalence reproduces
the original adjacency relation on P. Two compatible injections from
the same P into two graphs therefore yield the AgreeBase condition of
TaggedAmalgam. The compatibility/transport of finite strongness and
2-sparsity is the next proof obligation. Generic Fraisse construction
and functional closure expansion remain open.


## Transfer of sparse finite structures to their normal forms (verified)

Using a finite induced-equivalence of carriers, normalGraph_twoSparse_iff
and normalGraph_strong_base_iff identify 2-sparsity of the entire finite
graph and self-sufficiency of the base with their normal-form versions.
The proof depends on the previously audited induced-embedding invariance
and explicitly matches the image of the common base as well as the whole
finite vertex set. This allows the verified tagged strong-amalgamation
theorem to be applied to arbitrary finite strong embedding spans.


## Strong free amalgamation for arbitrary finite base embeddings (verified)

FiniteSpan.strong_amalgam_of_embeddings takes two finite 2-sparse
graph structures with a common abstract base P embedded injectively
and inducedly into both, and assumes the images of P are strong.
Using the verified normal-form equivalences, it constructs a tagged
free graph that is 2-sparse and whose canonical induced factor images
are strong. The original maps of P are respected by construction.
Once audited, this completes the finite strong-amalgamation calculation
for arbitrary spans. A countable strong Fraisse construction and the
functional-closure language are still not formalized.


## Explicit embeddings of the original graph structures (verified)

The canonical maps from A and B into the tagged carrier are the
inverses of the normalization equivalences followed by the two tag
inclusions. Both are injective, agree on the prescribed base maps,
and preserve and reflect the original adjacency relations.
Combining these maps with the verified abstract strong-amalgamation
theorem will give an explicit existential strong-amalgamation witness.


## Explicit finite strong free amalgamation (verified)

FiniteSpan.exists_finite_strong_free_amalgam constructs a graph K and
injective induced maps f:A→K and g:B→K for arbitrary finite 2-sparse
graph structures with compatible strong embeddings of an abstract
common base P. The maps commute over P; moreover, f(a)=g(b) occurs
only for one common base point. The two images are strong and K is
2-sparse. The proof factors through the normal-form equivalences
and the tagged strong free-amalgamation theorem. This is a direct
finite strong-amalgamation witness, not a claim about the generic limit.


## Certification of arbitrary finite strong free amalgamation

The [145-declaration Lean build and standard-axiom audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38020714173) passed at [source commit 2f6e5f1](https://github.com/janhubicka/lean-big-hrushowski/commit/2f6e5f1aed115c96f41cbf1f6f7d58654e8d24ba). Nineteen Lean files were checked for proof placeholders and none were found.

`FiniteSpan.exists_finite_strong_free_amalgam` gives, for arbitrary finite 2-sparse graph structures G and H and compatible strong induced embeddings of an abstract base P, an explicit tagged finite graph K and injective induced maps f:A→K and g:B→K. They agree over P; equality of an f-image and a g-image occurs only over the same point of P. The entire K is 2-sparse, and both image substructures are strong. This is the finite strong free-amalgamation theorem for C0 in the binary graph language.

The independent `check_abstract_amalgam.py` regression will test all 5,993 input spans with graph orders at most three and includes the K5-over-K3 obstruction when the strong-base hypothesis is dropped. Its status is pending the integrated CI run.

**Still open:** construction and genericity of the countable strong Fraïssé limit, the functional closure presentation, and the later Ramsey/Ellentuck results.


## The hereditary and joint-embedding properties of C0 (verified)

The finite graph class C0 is hereditary by its subset-wise definition.
The empty vertex set has predimension zero and is strong in any
2-sparse graph. Therefore the verified strong free-amalgamation
construction over an empty base produces a joint strong embedding
of any two finite 2-sparse graphs. This verifies the elementary
finite age properties, not the existence of the countable strong
Fraisse limit or its extension property.


The independent finite-age regression tests 76 labelled simple graphs of orders up to four and all 5,776 tagged disjoint joint embeddings. It also checks that K6 fails the 2-sparsity condition. Kernel compilation and the axiom audit remain the certification criteria.


**Certified checkpoint:** [PR CI run 38055132030](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38055132030) passed at [code commit cb99b36](https://github.com/janhubicka/lean-big-hrushowski/commit/cb99b366b2a073abd8ef3a130f668fbbd1e3f347). All 150 printed Lean declarations used only standard logical axioms; 20 Lean files were checked for proof placeholders. The new independent regression passed on 76 labelled graphs of order at most four and 5,776 tagged strong joint embeddings. The age's essential countability and its countable generic limit remain to be proved in Lean.


## Countability of labelled strong diagrams (verified)

FiniteCatalogue proves that, for each n, there are finitely many graph
relations on Fin n and that for fixed n,m the class of 2-sparse
strong embedding diagrams from Fin n to Fin m is finite. Their disjoint
union over n,m is countable. A canonical encoding/partial decoder is
chosen and every finite strong diagram appears at some numerical code.
This supplies a countable catalogue, but it does not yet schedule
requests against a growing chain or construct the generic limit.


## Repeated enumeration of potential strong extension requests (verified)

An extension request now consists of a labelled finite strong diagram
and a map of its source vertices into the natural-number carrier.
These requests form a countable set. Cantor pairing supplies a repeated
enumeration: for each request R and each threshold N, there is a stage
k≥N at which R is decoded. This is the fairness condition required
for requirements that only become applicable after a finite base is
present in the construction. Applicability and realization at a stage
remain separate tasks.


## Certified catalogue and fair-request encoding

The [passing 153-declaration Lean and axiom audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38055955615) at [source commit f113a49](https://github.com/janhubicka/lean-big-hrushowski/commit/f113a4930ad930163ae56de5a94404c673dc8d52) used only standard logical axioms. Twenty-one Lean source files passed the placeholder check, and all existing finite graph regressions passed.

The relevant theorems are `FiniteCatalogue.strongDiagram_occurs` and `FiniteCatalogue.fairRequest_after`. The latter shows that for every labelled strong diagram together with a proposed map to ℕ, and every threshold N, a schedule position k≥N decodes that request. A proposed map need not be an induced strong embedding at the time of its scheduled occurrence; applicability and successful response must be checked against the eventual construction.

**Not yet formalized:** every finite abstract strong span can be relabelled as a Fin n→Fin m diagram, and construction of a countable strong chain satisfying every applicable scheduled request. The countable catalogue alone does not establish genericity.


## Fair chain implies strong extension property (verified)

Given a graph on the natural-number carrier and a covering increasing
chain of finite strong induced subgraphs, an applicable request at stage
k is one whose source already embeds inducedly and strongly in stage k.
A local response strongly embeds the target in stage k+1, respecting
the given base map. If every applicable fair-scheduled request receives
such a response, the new theorem derives the strong extension property
of the whole graph: every globally strong induced finite source embedding
extends along each labelled strong finite extension diagram. The proof
uses the unbounded fairness lemma and global strongness of chain stages.
Existence of a chain satisfying the local response rule is not yet proved.


**Certification:** [successful CI run 38056485693](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38056485693) at [commit 59e6701](https://github.com/janhubicka/lean-big-hrushowski/commit/59e6701f9d0f5cd53b94bc9cb498a3891a02e54f) compiled and audited 154 declarations, using only standard logical axioms, with 22 Lean files passing the proof-placeholder scan. The theorem `FiniteCatalogue.strongExtensionProperty_of_fairResponses` explicitly assumes a covering finite strong-step chain and the local response obligation at each scheduled applicable request. Those hypotheses are not derived from the finite free-amalgamation theorem here. In particular no countable Fraïssé limit is constructed by this theorem alone.


## Completeness of labelled strong diagrams (verified)

Every induced strong embedding between finite 2-sparse graphs carried
by arbitrary finite types has a presentation in the countable catalogue
StrongDiagram (card A) (card B). The chosen equivalences Fin(card A)≃A
and Fin(card B)≃B transport adjacency, 2-sparsity, and the strong
embedding relation, and identify the labelled embedding with the
original map. This closes the finite relabelling obligation, but
does not construct a countable chain or realize fair requests.

The [Lean audit run 38061458133](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38061458133) compiled the labelled-diagram completeness theorem and audited 154 declarations, with only standard logical axioms and no proof placeholders in 22 files. The theorem has explicit Fin(card A)≃A and Fin(card B)≃B witnesses preserving the source and target adjacency relations and identifying the original induced strong map with the labelled one. No claim is made that the fair response schedule is realized by a countable graph.


## Arbitrary finite extension from the labelled criterion (verified)

The new theorem derives the extension property for every finite
2-sparse induced strong embedding A→B with arbitrary finite vertex
types from the labelled strong extension property in the countable
ambient graph. It uses the proved completeness of labelled diagrams,
transports the given globally strong base map into a concrete fair
request, applies the labelled extension hypothesis, and transfers the
resulting embedding back to B. The countable ambient graph itself,
and a chain satisfying local fair responses, remain unconstructed.


**Certification:** [successful 156-declaration CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38062233519) at [code commit b3d5265](https://github.com/janhubicka/lean-big-hrushowski/commit/b3d5265a83cae05dfab96d7b8d71caadcdb18d28), standard logical axioms only, with 24 Lean files free of proof placeholders. `FiniteCatalogue.arbitrary_finite_strong_extension` takes arbitrary finite 2-sparse graphs, a strong induced finite extension, and a globally strong induced source embedding into a graph M on ℕ. Under the explicit labelled extension property hypothesis on M, it constructs an induced globally strong embedding of the target extending the source embedding. No countable generic M is constructed, and the labelled extension-property hypothesis is not discharged here.


## Fresh natural-number labels for finite successor stages (verified)

For any injective map f:A→B of finite carriers and any injective
labelling e:A→ℕ, `extendNatLabels` constructs an injective labelling
of B extending e along f. Each vertex outside f(A) receives a label
larger than every old label. This supplies a fixed natural-number
carrier interface for a future chain of finite strong embeddings.
Graph adjacency and the construction of a fair responding chain are
not yet included in this theorem.

The [160-declaration Lean CI audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38062409525) compiled the finite injection extension lemmas with only standard logical axioms and no proof placeholders. The independent `check_fresh_nat_labels.py` regression checks old-label preservation, freshness above the old maximum and injectivity across many finite maps. CI on the combined branch head will certify this additional regression.


## Finite strong graph stages on the Nat carrier (verified at PR head)

`GraphOn.transportedToNat` transports a finite graph along any
injective map into ℕ and has no edges outside the image. It preserves
induced adjacency, predimension, 2-sparsity, and finite strongness.
Combined with the fresh-label theorem, it yields
`FiniteSpan.exists_fresh_strong_nat_stage`: every finite strong
extension A≤B can be represented as a finite graph stage on ℕ
with all existing A labels fixed, distinct fresh labels for B\A,
and a strong inclusion of the old finite stage domain.
The construction of a compatible countable sequence and realization
of fair requests are not yet formalized.

The additional `transportedToNat_agree_on_old` theorem states that
transporting a finite strong induced extension to fresh Nat labels
does not change any edge or nonedge between previously labelled
vertices. This is the graph-coherence invariant needed for a
direct limit of successive finite stages. CI verification pending.


The [combined Lean CI and axiom audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38063216441) passed for PR #21 at commit `c0b9c4e`. Integration with the post-PR-19 main branch is subject to a fresh run.


**Adversarial carrier-coverage warning (10 October 2026).** `extendNatLabels` is injective and fresh, but its successive images need not cover ℕ. For the empty source and a singleton target it assigns label 1; every later genuinely new label exceeds the current maximum, so 0 remains uncovered. The existing `Predimension.StrongChain` requires `∀ x : ℕ, ∃ n, x ∈ stage n`, which cannot be deduced from these finite-stage theorems. To complete genericity one must use consecutive initial segments with unbounded stage sizes, or build the direct limit on a separately defined countable carrier and then reindex it. This is a gap in the countable construction, *not* in the finite strong-amalgamation proof.


## Initial-segment carrier repair (certified)

`InitialSegmentLabels.lean` replaces the old maximum-plus-one labelling by
an equivalence `B ≃ Fin (card B)` extending a prescribed equivalence
`A ≃ Fin (card A)` along an injection `A → B`. The finite carrier splits
into the old vertices and a tagged fresh tail by `FiniteSpan.splitEquiv`,
which has already been Lean-certified. The intended results assert that
all old numeric labels are preserved, the new map is injective and its image
is **exactly** `Finset.range (card B)`. No gap can survive in the finite
carrier. These results are not yet certified, and they do not construct the
countable fair responding chain or prove that stage sizes go to infinity.

The independent finite-model regression checks old sizes at most five,
new sizes at most six, all injections and all old initial-segment
bijections (114,324 diagrams), including empty sources and targets.
It is a diagnostic and cannot certify the unrestricted Lean theorem.


## Finite local response for fair strong diagrams (certified)

`FiniteCatalogue.exists_finite_strong_response` instantiates the
already-certified arbitrary finite strong free-amalgamation theorem with
a labelled `StrongDiagram n m` and an induced strong embedding of its
source into an arbitrary finite two-sparse stage. It produces a two-sparse
finite amalgam with induced strong embeddings of both the stage and the
target, commuting exactly on the prescribed source. The two images
intersect only over that source.

This discharges the **local finite response existence** obligation.
It does not yet give a coherent sequence of Nat-labelled finite stages,
a graph on their union, or the fair-response property in that union.
The 173-declaration [successful Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38078587574) verifies this theorem; the full coherent countable construction remains open.


## Growth by a fresh strong vertex (certified)

`GraphOn.onePointGraph_sparse` shows that the graph on one isolated
vertex is 2-sparse. The theorem
`FiniteSpan.exists_fresh_strong_extension` freely amalgamates this
singleton with any finite two-sparse graph over the empty strong base.
It yields a finite two-sparse extension in which the old graph is an
induced **strong** subgraph and there exists a vertex outside its image.
This provides an explicit strict-growth input for the countable
construction, even if an applicable scheduled request adds no vertices.

The theorem relies on the verified tagged amalgamation's
no-unintended-identifications conclusion. It does not itself
realize scheduled requests, construct a chain or a direct limit.

## Direct-limit graph of coherent finite stages (certified)

`CoherentNatGraphStages` packages finite supports on ℕ, a finite-edge
stage graph, one-step support inclusion, exact old-old adjacency and
nonadjacency agreement, and **explicit coverage of all Nat vertices**.
The theorem `CoherentNatGraphStages.limitGraph_induced` constructs
the graph with adjacency `∃ n, (graph n).adj x y` and proves that its
restriction to any finite stage is exactly that stage's graph.
`agrees_of_le` and `edge_mono` extend the successor invariants to
arbitrary later stages.

The construction is **conditional on coherent stage data**. A coherent
strong, growing, fair-response chain is still to be built; this
module does not infer it from finite amortization or genericity.

## Finite induced adjacency transfer (certified)

`GraphOn.edgesWithin_eq_of_agreeOn`,
`GraphOn.predim_eq_of_agreeOn`, and
`GraphOn.isStrong_iff_of_agreeOn` compare two arbitrary ambient
graphs on one vertex type that have the same **induced** graph
on a prescribed finite set. They prove equality of unordered finite
edge sets, predimensions, and relative strongness of an included
finite subset. No assumption is made about graph edges outside the
larger finite set.

This is needed to transfer local strong successor steps from a
coherent stage graph to the direct-limit graph. It does not construct
the coherent stages. CI verification of this module remains pending.

**Combined integration:** The growth and graph-union source heads passed independently in GitHub Actions runs [38078931390](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38078931390) and [38079104902](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38079104902), auditing 174 and 176 declarations respectively. The finite induced-transfer module and full consolidated build require a fresh integrated CI result. No countable stage system has yet been constructed.


## Conditional strong countable limit (certified)

`CoherentNatGraphStages.asStrongChain` assumes the finite support of
each stage is strong in the next stage graph. The induced-subgraph
agreement of the graph union, plus the finite strongness-transfer
lemma, yield a `Predimension.StrongChain` in the countable limit.
Consequently `stage_global_of_strong_steps` proves all finite
stages globally strong and `finiteStrongCover_of_strong_steps`
supplies a finite strong cover. If every stage is two-sparse,
`limit_predim_nonneg_of_sparse_stages` proves the union's
predimension is nonnegative on every finite set.

The coherent growing fair-response stage system still has to be
constructed. This is *not* a proof of the existence of the generic
countable Hrushovski graph without that hypothesis.


## Gap-free increasing stages cover ℕ (certified)

The `NatStageCoverage` module proves that every strictly increasing
sequence of finite stage sizes satisfies `n ≤ size n`. Consequently
the consecutive domains `Finset.range (size n)` are increasing and
their union is all of ℕ. This gives the carrier-coverage implication
needed to instantiate `CoherentNatGraphStages.covers` from the
strict-growth theorem and initial-segment relabelling. No continuous
or global stage existence is asserted by these arithmetic lemmas.


## Certified integrated coherent-limit checkpoint — 10 October 2026

The [passing CI and standard-axiom audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38079857370)
at source [commit a0f5fd3](https://github.com/janhubicka/lean-big-hrushowski/commit/a0f5fd36f50c595bab0d2b06af2209968b05545d)
compiled the complete finite-age, carrier, response, and conditional
strong-limit development. The audit checked **188 declarations**, all
depending only on standard Lean logical axioms, and scanned **33 Lean
files** for proof placeholders. All existing finite regression tests,
including the 114,324 gap-free initial-segment diagrams, passed.

The exact endpoints now include:
- `FiniteCatalogue.exists_finite_strong_response`: a finite strong
  amalgam answering an applicable labelled extension diagram;
- `FiniteSpan.exists_fresh_strong_extension` and
  `FiniteSpan.initialSegment_stages_cover`: strict growth and
  coverage of Nat by consecutive initial segments;
- `CoherentNatGraphStages.limitGraph_induced`: finite stages remain
  induced in the graph union;
- `GraphOn.isStrong_iff_of_agreeOn`: finite strongness transfers
  between ambient graph predicates agreeing on the induced container;
- `CoherentNatGraphStages.stage_global_of_strong_steps`,
  `finiteStrongCover_of_strong_steps`, and
  `limit_predim_nonneg_of_sparse_stages`: a **given** coherent covering
  chain of finite strong, two-sparse stages has the required strong
  and two-sparse countable limit.

**Still not proved:** the existence of one coherent *fair responding*
sequence of finite stages, formed recursively from the finite responses,
with initial-segment relabellings and strict growth. This is the
remaining gap before instantiating
`strongExtensionProperty_of_fairResponses` for a concrete countable
Hrushovski graph. Nothing in the new conditional transfer proves
Ramsey, big Ramsey degree, or Ellentuck statements.
