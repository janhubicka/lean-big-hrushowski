# Adversarial foundation audit (9 October 2026)

The independent checks below are distinct lines of attack performed on the
same development; they are NOT claims of independent external human refereeing.

## A. Predimension and edge-count referee — pass (finite scope)

- A graph edge is a two-vertex unordered Finset and is counted exactly once.
- The edge count in P union Q includes possible crossing edges not seen in
  either P or Q. Hence it is **supermodular** and δ is **submodular**.
- Graph submodularity is proved from the edge-count identity, not postulated
  for graph objects. The abstract Predimension structure is used only after
  that concrete theorem.
- Exhaustive independent bit-set calculations cover all 1,100 labelled
  simple graphs of orders 0 through 5: 1,065,509 pairs of vertex sets.

## B. Strong vs strict closure referee — pass (finite scope)

- IsStrong requires non-strict inequalities δ(A) <= δ(X) on extensions.
  IsDClosed requires strict inequalities for *every proper* extension.
- A two-edge path on vertices 0,1,2 has A={0,2}, the two endpoints,
  and C={0,1,2}. Here δ(A)=4=δ(C); A is strong in C but not d-closed. The reverse
  implication is therefore invalid.
- Finite intersection and transitivity are proved separately for the two
  predicates. The strict proof branches on the intersection with the
  intermediate base and never silently weakens the strict inequality.
- Exhaustive finite regressions cover 2,840,863 strong intersections,
  973,356 strong transitivity cases, 1,753,601 strict intersections,
  686,097 strict transitivity cases, and 204,415 cases of strict =>
  non-strict closure.

## C. Closure existence referee — pass with a defined boundary

- A finite family of strong subsets of one finite ambient graph has a
  strong intersection. Taking all strong supersets of A gives a least
  strong hull in this ambient graph.
- In M_0, the existence of a finite strong container, independence of the
  container, and the agreement with algebraic closure require additional
  arguments. They have **not** been inferred by the formalization.
- Strict d-closure finiteness in the C_F class and its uniform F-inverse
  bound are independent, later proof obligations.

## D. Lean kernel / build referee — pass

- The pinned toolchain matches partite-construction (Lean 4.35.0-rc3,
  successor-tree dependency at ce5ce187).
- [CI for finite hulls](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/37977945496)
  compiled the project, audited 15 theorem declarations, and detected no
  admitted proofs. All theorem axioms were contained in the standard set
  propext, Classical.choice, Quot.sound.
- A caution: the abstract Predimension declaration *assumes*
  submodularity. The graph instance supplies a separately proved theorem.

## E. Manuscript and validation annotation referee — pass with limits

- Manuscript PR #36 distinguishes structures from their vertex sets, keeps
  the existing graph/functional closure conventions, and uses the same
  green, orange, blue markers as the Ramsey survey.
- Green annotations are confined to finite-predimension results whose
  Lean counterparts have passed CI. The countable-model extension of the
  finite-hull assertion remains orange; the Ramsey, level, and Ellentuck
  theorems remain unmarked.
- The review-only validation overlay is disabled in the circulation build.
  The TeX macros were smoke-tested separately, but the complete v52
  manuscript was **not** freshly typeset in this tool environment.

## Next targets

The finite predecessor core is now ready. The next honest proof boundary
is a formal definition of an increasing strong exhaustion of M_0, with
the induced finite closure and its invariance under inclusion of strong
containers, before encoding enumeration increments.


## New adversarial passes: closure increments and finite decompositions

**F. Minimal-choice reviewer.** A chosen vertex minimises the cardinality
of its generated finite closure, not the cardinality of the entire ambient
strong requirement. Any generated closure properly contained in that
of the chosen vertex would have smaller cardinality. This proves
inclusion-minimality, without asserting that the resulting closures
are linearly ordered.

**G. Intermediate-strongness reviewer.** An intermediate Z strong inside
the new finite globally strong block is itself globally strong, by
transitivity. If Z properly extends the old prefix, it contains a new
vertex; the whole block lies in the closure of the prefix and that vertex.
Therefore Z is the full block.

**H. Finite-decomposition reviewer.** Each step adds the chosen vertex,
so D minus the new prefix is a proper subset of D minus the old prefix.
The induction decreases a natural cardinality, not the predimension.
The theorem does not schedule the countably many generic extension
requirements of M_0.

**I. Diagnostic reviewer.** A separate bit-set implementation checks
every labelled graph on at most five vertices. In the initial exhaustive
run there were 189,941 globally strong source/container pairs and
310,904 minimal increments, with no counterexample. The CI checker is
retained as a regression test. These are computational checks, not
additional Lean theorems.

The above are independent *review questions* applied by the same
assistant, not external or human referees.


## Finite cover and countable exhaustion — adversarial review

**A. Existence of a stage.** Every finite set has a finite globally strong cover; the next selected container includes the previous stage and the next enumerated vertex. The sequence is increasing by literal subset inclusion.

**B. Exhaustiveness.** A surjective map from the natural numbers reaches every vertex. The constructed stage at index n+1 includes the enumerated vertex at n.

**C. Container independence.** Finite hulls computed in two globally strong containers are equal, so using arbitrary classical choices of containers does not affect closure.

**D. Hypothesis boundary.** This result does not prove the finite-strong-cover property for the Hrushovski limit; that follows from construction as a union of finite strong substructures, which is not formalized as an actual model yet.

**E. Conditional strength.** The equivalence between finite strong covers and strong exhaustions requires a surjective countable enumeration in the forward direction. It is not claimed for arbitrary uncountable ambient vertex sets.

These are deliberately separated checks by the same assistant, not independent external reviewers.


## Back-edge bound: adversarial review

1. **Edge-count orientation:** edges are finite unordered two-element sets. Insertion adds exactly the old-to-new incident edges, not twice their number.
2. **Sign:** predimension changes by 2 minus the incident-edge count; self-sufficiency forces this increment to be nonnegative.
3. **Equality case:** when two incident edges are present, the one-point extension has the same predimension as the old prefix, and is strong inside the generated hull.
4. **Global closure:** the singleton conclusion uses transitivity and an explicitly supplied strong exhaustion. It does not prove that the concrete Fraïssé limit has this exhaustion.
5. **Neighbour interpretation:** the identification of incident edges with old neighbours uses that the graph is simple; the separate Lean bijection is a future interface proof.

These are distinct hostile reviews by one assistant, not independent external referees.

**Infinite-graph interface attack:** The current `FiniteGraph V` stores a finite *global* edge set; the countable generic Hrushovski graph has infinitely many edges. Therefore the C0 proof is fully checked for its finite combinatorial statement, but does not constitute a direct formal proof about the entire countable graph. Finite strong-container transfer is not yet formalized. The manuscript marker is orange for this reason as well as the neighbour/edge correspondence.


## Infinite graph versus finite view — adversarial audit

**Representation reviewer:** GraphOn uses a symmetric, irreflexive adjacency predicate without requiring the global edge set to be finite. Its induced edges are finite pairs enumerated inside each finite vertex set.

**Predimension reviewer:** for P and Q, induced crossing edges occur only in their union; the edge count is supermodular and delta is submodular. No global graph finiteness is used in this argument.

**Restriction reviewer:** the finiteView graph on S has exactly the same edge instances on every T subset S. Its predimension and finite strongness therefore agree literally with those computed in GraphOn.

**Closure reviewer:** the two-edge singleton-closure theorem assumes a genuine StrongExhaustion of the infinite graph's predimension. That exhaustion is not constructed for M0 in this PR.

**Terminology reviewer:** the numerical theorem counts incident unordered edges; the equivalence with the number of earlier neighbours in a simple graph is mathematically canonical but has not been formalized as a standalone Lean bijection.

**Kernel reviewer:** all seven infinite-graph core declarations and four transfer declarations are included in the passing standard-axiom and placeholder audit at the 67-declaration checkpoint.

These are separate hostile review perspectives by one assistant, not separately spawned model/human referees. No new mathematical defect was identified within the stated proof boundaries.


## Adversarial review: old neighbours and unordered back edges

**Referee A — representation.** A graph is a symmetric irreflexive
adjacency predicate; unordered edges are two-element sets. Parallel
edges and loops are impossible. The lemma would need revision for
multigraphs, and deliberately assumes a simple graph.

**Referee B — domain.** The new vertex is required not to belong to
the old set. This prevents a back edge from being counted among the
already existing edges and establishes the two-element-pair cardinality.

**Referee C — surjectivity.** Every incident edge contains the new vertex
and precisely one other endpoint. The endpoint is old, and the adjacency
orientation can be reversed using graph symmetry.

**Referee D — injectivity.** Different old neighbours yield different
unordered pairs with the new vertex because neither equals that vertex.
The cardinality equality therefore counts each old neighbour exactly once.

**Referee E — finite regression.** The independent bitset implementation
tests all 1,100 labelled simple graphs of orders 0 through 5 and all
84,073 old-set/new-vertex configurations. It compares the literal sets
of incident edges as well as their cardinalities.

**Referee F — manuscript transfer.** The counting identity needs no
Fraisse genericity. The closure statement still assumes an actual
strong exhaustion and must not be marked as a concrete model theorem
until its existence is connected to the Hrushovski construction.

These are independent adversarial *questions* examined by one assistant,
not separately spawned external or human referee agents.


## Adversarial review: local strong chains versus global strongness

**Referee A — predimension.** The chain relation is self-sufficiency
in the same fixed predimension on finite subsets of the union. No
unjustified change of edge set is permitted when passing to a later stage.

**Referee B — transitivity.** The induction uses only the previously
audited transitivity of IsStrong and reflexivity in the equal-index case.
The successive steps do not need to be strictly increasing.

**Referee C — coverage.** Every finite test set is contained in a later
stage because each of its finitely many vertices belongs to some stage
and the stage domains are increasing.

**Referee D — global strongness.** For a test extension X of stage n,
choose a stage covering stage n union X and then a stage no earlier
than n. Strongness in that later stage gives the required inequality.

**Referee E — counterexample discipline.** If the successive inclusions
are not strong, coverage alone proves nothing: the strong-step hypothesis
is essential and remains explicit in the Lean structure.

**Referee F — computation.** The independent checker exhausts every
labelled simple graph of size at most four and every three-stage covering
chain of strong inclusions, and tests the global conclusion (5,074 cases).

**Referee G — limit boundary.** No model of the generic Hrushovski limit
or its extension property is constructed. The verified implication is
the direct-limit lemma that will be applied to such a construction.

These are separated hostile proof checks by the same assistant, not
external or human referees.


## Adversarial review: free-amalgamation predimension

**Referee A — edge accounting.** The no-crossing hypothesis is a finite
edge-set inclusion, not an assumption that the two vertex sets are
disjoint. It allows overlap, and that overlap is subtracted exactly once.

**Referee B — hereditary restriction.** When the right factor is shrunk,
it must continue to contain the full original overlap. Otherwise a
previously internal edge of the right factor could become a crossing
edge and the modular identity may fail. The Lean restriction lemma
retains this indispensable assumption explicitly.

**Referee C — strongness direction.** To prove A strong in A union B, the
required hypothesis is P strong in B, where P=A intersect B. The
corresponding implication is symmetric when A and B are exchanged.

**Referee D — predimension scope.** Only finite vertex sets are counted,
even when the ambient graph has infinitely many vertices or edges. The
lemma does not assume the whole graph has finite edge support.

**Referee E — genericity.** This proves an amalgamation *calculation*,
not existence of a free amalgam of arbitrary structures, preservation
of 2-sparsity for the full amalgam, or the Fraisse extension property.

**Referee F — independent finite regression.** Every labelled simple
graph on at most five vertices was tested. There were 635,495
no-crossing pairs and 624,416 successful strongness-transfer cases for
each orientation, with no counterexample.

These are separately designed hostile review tests performed by the
same assistant, not externally independent human or model referees.


## Adversarial review: 2-sparsity under strong free unions

**Referee A — quantification.** A 2-sparse graph means every finite
induced subset has nonnegative predimension, not merely the whole
finite structure. The Lean definition quantifies over all subsets.

**Referee B — predimension scope.** The ambient graph can be infinite,
but every induced edge count and all union factors in this argument
are finite. There is no hidden global-edge-finiteness assumption.

**Referee C — overlap.** The no-crossing hypothesis is inherited by
the restrictions of both factors to the same test vertex set. Their
intersection is counted once in the modular identity, and its
predimension is compared with the right part by self-sufficiency.

**Referee D — strongness direction.** The hypothesis for preserving
2-sparsity of A union B is that A is 2-sparse and A intersect B is
strong in B. The symmetric statement is separately proved. One
must not replace this by an arbitrary common induced subgraph.

**Referee E — boundary.** These are no-crossing configurations inside
a given graph. Universal availability of a free amalgam with no new
identifications and existence of the Fraisse limit are not proved here.

**Referee F — independent finite computation.** All 1,100 labelled
graphs of size at most five were checked. The test covers 635,495
no-crossing pairs, 624,416 2-sparsity-preserving pairs in each
direction, and 244,695 strong extensions of sparse bases.

These are hostile review questions checked by the same assistant,
not independent external human or model referees.


## Concrete free graph join: independent adversarial checks

**Referee 1 — common-base compatibility.** The construction is defined for
two graph predicates on one carrier. The resulting induced graph agrees
with each factor only when their adjacency relations agree on every pair
of vertices in the intersection. This hypothesis must not be omitted.

**Referee 2 — absence of accidental edges.** Every edge of the join is
inherited from one factor and both endpoints belong to that factor. No
new crossing edge occurs. Edges outside the union are discarded.

**Referee 3 — duplicate identification.** The shared vertices are already
the intersection a∩b. This stage does not rename disjoint tails or prove
that arbitrary abstract embeddings can be represented on this carrier.
That transport is a separate, explicitly unverified part of full
amalgamation.

**Referee 4 — finite subset test.** 1,052,741 graph/vertex-subset pairs
were examined exhaustively for labelled graphs up to four vertices.
894,763 compatible inputs preserve the factor induced edge sets, and
893,483 instances satisfying both 2-sparsity and strong-base conditions
give 2-sparse unions in which both factors are strong.

**Referee 5 — logic and scope.** The resulting graph is symmetric and
irreflexive by construction, and the argument counts unordered edges.
The Fraisse extension property and the functional closure expansion
are not consequences of this graph construction alone.

These are separate adversarial questions and an independent calculation,
not a panel of independently spawned external referees.


## Strong free join: second adversarial audit

**A. Factor embeddings.** Join edges occur only inside either factor. Exact agreement on the overlap is indispensable: without it, an edge present in one factor might appear in the other induced factor.

**B. Edge cardinality.** The no-cross proof uses that every edge has two distinct endpoints. Its witnesses span the edge, so it lies wholly in one of the two factors.

**C. Strongness direction.** To keep A strong in A union B, the overlap must be strong in B, not merely in A. Both directions are checked separately and each predimension is transported from its original factor.

**D. Subset-wise 2-sparsity.** The theorem proves nonnegative predimension for every induced subset of the join, not only for the full union.

**E. Negative counterexample.** A common K3 has predimension 3, while each K5 extending it has predimension 0. Gluing two K5's over K3 without strongness yields seven vertices and seventeen edges, giving -3. Both input K5 graphs are 2-sparse. The strong-base assumption matters.

**F. Abstract carrier warning.** The joined pieces have already been identified along their overlap. No fresh disjoint carrier for arbitrary abstract base embeddings has been constructed in Lean yet.

**G. Kernel and finite-model checks.** The 102-declaration build passed, and the independent bit-mask implementation checked 894,763 compatible inputs. Neither result alone verifies the Fraisse generic extension property.

These are distinct adversarial proof perspectives carried out by the same assistant and computational cross-checks; not human referee reports.


## Tagged carrier: adversarial review

**Reviewer A — identification.** The output carrier is P+(L+R);
the canonical inclusions are injective and their only overlap is P.
No two vertices from the fresh tails can be identified.

**Reviewer B — common-base compatibility.** The two input adjacency
relations must agree on P. Without this, an edge in one input could
appear as an unwanted induced edge of the other.

**Reviewer C — induced nonedges.** Preserving only input edges is
insufficient. The proofs of both graph embeddings use the agreement
hypothesis to reflect every adjacency and hence every nonadjacency.

**Reviewer D — no crossing.** The left edge witnesses come exclusively
from P+L and the right ones exclusively from P+R. A left-tail to
right-tail edge is impossible by the disjoint tagged constructors.

**Reviewer E — scope.** This is a normal-form graph amalgam for an
abstract shared base. Strongness of the two canonical embeddings for
finite 2-sparse input graphs must still be transferred through these
tags, and no Fraisse genericity has been proved here.

**Reviewer F — exhaustive regression.** Every labelled graph pair in
normal form with |P|,|L|,|R| at most 2 is checked. There are 5,613
inputs and 2,875 compatible diagrams. Factor preservation and no
crossing hold in every compatible diagram; 2,729 strong 2-sparse
cases satisfy the intended later strong-amalgamation property.

These are separated adversarial reviews by the same assistant,
not independent external referee reports.


## Induced embeddings: adversarial review

**Referee A — nonedges.** An injective map preserving only graph edges
is insufficient. The adjacency hypothesis is an equivalence, ensuring
that no new induced edge appears between image vertices.

**Referee B — injectivity.** Without injectivity, two distinct vertices
can collapse and the vertex cardinality changes. Injectivity is also
needed to make the image operation injective on unordered edge sets.

**Referee C — edge extraction.** An edge contained in the image of a
finite set has a finite filtered preimage whose image is precisely
that edge. This is why the edge sets, not merely their counts, agree.

**Referee D — finite intervals.** Every intermediate substructure of
the image is a filtered image of an intermediate substructure of
the source. Hence the strongness relation is preserved and reflected;
checking only the two endpoints would not suffice.

**Referee E — 2-sparsity.** The theorem is for *every* induced finite
subset; its invariance follows from the same filtered preimage, not
only from invariance of the full finite graph.

**Referee F — independent regression.** Every simple labelled graph
of order at most four, every indicated injection into a one-point
larger target and four exterior edge patterns are tested. The checker
covers 497,876 predimension equalities and 2,509,516 finite interval
strongness equivalences, including negative controls for noninjective
and noninduced maps.

**Referee G — scope.** This supplies the predimension transport needed
for the tagged amalgam, but strong amalgamation of arbitrary diagram
embeddings still requires matching the canonical images and common base.

These are hostile questions independently selected by one assistant,
not reviews by independent human referees.


## Tagged strong free amalgamation — adversarial audit

**1. Shared-base identity.** The left and right images have intersection equal to the image of P, not merely a superset thereof. The proof uses the exact overlap lemma from TaggedAmalgam and does not identify tail vertices across factors.

**2. Strongness direction.** To establish leftDomain strong in the join, the base must be strong in the right input; conversely the right factor needs strongness in the left input. Both source assumptions are transported by the proved finite induced-embedding equivalence, and both are used in the final theorem.

**3. Predimension comparison.** Edge sets and predimension on each tagged factor agree with those in its source graph, including induced nonedges. No claim that an arbitrary edge-preserving but non-induced map preserves strongness is made.

**4. Every induced subset.** The conclusion uses GraphOn.IsTwoSparse, which quantifies over all finite subsets of the tagged carrier, not just its entire vertex set. Modular predimension and strong embedding provide that conclusion.

**5. Necessity controls.** Without source agreement on P, the induced graph embeddings can fail. Without a strong common base, gluing two K5 graphs over K3 gives a graph of predimension -3. Both obstructions are retained as independent computational regressions.

**6. Finiteness and universes.** The theorem assumes finite P,L,R to form the canonical finite domains; the graph adjacency itself is not required to be a finite global edge set. Its output is an actual graph on P⊕(L⊕R).

**7. Fraïssé interface.** The theorem is a complete strong-amalgamation statement for finite *tagged normal-form diagrams*. It is not yet a formal proof that every abstract finite embedding span reduces to this normal form, nor a construction of a countable generic limit or its extension property.

**8. Lean certificate.** The exact theorem statement and all its dependencies compiled in [CI run 38019222909](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38019222909). The audit found only standard logical axioms and no proof placeholders. These are adversarial perspectives carried out by one assistant, not separately spawned external human or model referees.


## Arbitrary finite embedded spans: adversarial review

**Referee A — exact image normalization.** Each injective base map extends to a literal equivalence P⊕Tail(i)≃A. The inverse puts the original vertices into the tagged carrier without collapsing tails.

**Referee B — induced embeddings.** Both output maps preserve *and reflect* adjacency, including nonedges. Agreement on the abstract base is a prerequisite, and the output maps identify no vertices except corresponding points of P.

**Referee C — strongness orientation.** The base is strong in each source, separately. Transport along the induced equivalences gives strong common bases in the normalized inputs; the tagged theorem uses the opposite input for each strong inclusion.

**Referee D — all finite subgraphs.** K.IsTwoSparse means nonnegative predimension for every finite induced subset, not just K itself.

**Referee E — original-domain images.** The proof establishes exact equalities between the images of the original A and B and the tagged left and right domains before concluding their strongness. The conclusion is not merely about anonymous normalized copies.

**Referee F — necessity.** Without a strong common base, gluing two K5 graphs over a K3 gives δ=-3. The theorem does not weaken this assumption. Without graph agreement on P, inducedness fails.

**Referee G — Lean kernel.** The complete explicit existential amalgamation theorem is included in the 145-declaration [passing audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38020714173). Only standard logical axioms occur; no proof placeholders were accepted.

**Referee H — boundaries.** This is finite strong free amalgamation for the predimension class C0. It does not construct its countable strong Fraïssé limit, its generic extension property, the functional closure expansion, or any big Ramsey theorem.

These are eight independent lines of hostile checking performed by one assistant, not an independently spawned external panel.


## Adversarial audit: finite strong age axioms

**Heredity.** IsTwoSparse requires nonnegative predimension for every induced subset; restriction to a smaller vertex set therefore preserves the condition. A claim about only the whole-graph predimension would not suffice.

**Empty strong base.** Graph predimension of the empty set is zero. For every induced extension X in a 2-sparse graph δ(X)≥0, hence the empty set is self-sufficient. This is exactly the condition needed to specialize finite strong free amalgamation to joint embedding.

**Freshness.** The inherited tagged free-amalgamation theorem introduces disjoint tails; the embeddings of two unrelated input graphs need not intersect even if their original vertex labels coincide.

**Computational cross-check.** All 76 labelled simple graphs on at most four vertices were checked for subset-wise 2-sparsity and empty-base strongness. Each of the 5,776 pairs was freely joined with tagged disjoint carriers and both inclusions checked to be strong. K6, of predimension -3, serves as a negative sparsity control.

**Boundary.** These results do not construct a countable generic graph or prove realization of every finite strong extension. Countability of finite isomorphism types and fair scheduling of extension requirements remain explicit tasks.

The hostile checks are separate questions assessed by one assistant, not independent external referees.


## Countable strong-diagram catalogue: adversarial review

**Finite relation reviewer.** On Fin n there are only finitely many binary adjacency predicates. A symmetric, irreflexive graph is determined by such a predicate; its proof fields carry no further data. The finite instance is obtained by an injective forgetful map, not by assuming graph finiteness axiomatically.

**Finite diagram reviewer.** For fixed n,m, source graph, target graph and embedding function belong to finite types. Injectivity, induced adjacency, 2-sparsity and strongness are proposition-valued fields. Thus the diagram type is finite even though not every map qualifies.

**Countability reviewer.** The union over n,m is countable. The choice of encoding is noncomputable, which is sufficient for countable existence but not a verified executable enumeration.

**Fairness reviewer.** Cantor pairing has a proved inverse and `Nat.right_le_pair`, so pairing the request code with an arbitrary threshold N gives a slot k≥N decoding that request. This is strictly stronger than mere occurrence at one unspecified time.

**Applicability reviewer.** Potential maps of source vertices into ℕ are deliberately unrestricted. The schedule includes maps that may fail to be injective or induced; the future construction must test applicability and satisfy only valid requirements.

**Completeness reviewer.** The code handles all labelled diagrams on finite ordinal carriers. A separate representative theorem is needed to identify every finite abstract strong-extension span with a labelled diagram; no such completeness is silently assumed.

**Genericity reviewer.** A fair request schedule by itself does not produce any graph, prove that every valid request is realizable at its scheduled stage, or construct the Fraïssé limit.

**Lean reviewer.** The [153-declaration CI audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38055955615) passed with only standard axioms, no placeholders, and all previous regressions. These are distinct hostile review perspectives carried out by the same assistant; no external independent referee agents were available or represented as having participated.


## Conditional genericity criterion — adversarial scope audit

**Fairness.** For every concrete encoded request and every threshold, the pairing-based enumeration yields a later stage carrying that same request. This is more than a one-time occurrence and is necessary because a source embedding may become available only after the requested base has appeared.

**Applicability.** A scheduled request is acted on only when its source map is injective, induced and strong inside the current stage. Arbitrary potential maps are intentionally allowed in the schedule; invalid requests impose no obligation.

**Global-to-local transfer.** For a globally strong finite source, cover its image by a finite stage; choose a later scheduled occurrence; global strongness restricts to that later stage. No implicit global extension assumption is invoked.

**Local-to-global transfer.** A response embeds the target strongly into the next finite stage. `StrongChain.stage_global` makes that stage globally strong, so transitivity yields the required globally strong image of the target.

**Genericity boundary.** The theorem does not construct the stages, realize the scheduled requests, prove that all finite diagrams are labelled by `Fin n`, or derive full Fraïssé homogeneity. Those are explicit, separate proof obligations.

**Machine check.** The exact theorem was included in the [154-declaration audited run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38056485693), with standard axioms and no admitted proofs. These hostile reviews are separate mathematical checks carried out by one assistant, not independent external human referees.


## Finite strong-diagram completeness — adversarial review

**Labelling:** The chosen Fin(card A) and Fin(card B) presentations are equivalences, so the vertex counts and all induced adjacency and nonadjacency statements are preserved. No canonical labelling is claimed.

**Strongness:** The target-side predicate is checked on every intermediate finite substructure. Under the target equivalence, the labelled image of the base is exactly the original image of the source map. Thus the strongness predicate is not inferred merely from nonnegative full-graph predimension.

**Source and target sparsity:** Each is transferred through the separately audited 2-sparsity invariant for induced embeddings; every induced subset is covered.

**Enumeration boundary:** The theorem asserts existence of a labelled representative for a given finite strong embedding. It neither chooses labels uniformly in the source graph nor constructs a countable chain answering requests.

**CI boundary:** The theorem and all dependencies compiled in [run 38061458133](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38061458133); the axiom audit reported only standard logical axioms and no placeholders. These are separate hostile review perspectives applied by one assistant, not external independent human referees.


## Removing finite labels from the conditional extension property — adversarial audit

**Catalogue completeness.** A finite strong extension is represented by a genuine labelled diagram with equivalences for both vertex carriers, preserving all induced edges and nonedges and the strongness of the source image in the target.

**Source re-labelling.** The given map from the original source into ℕ composes with its labelling equivalence. Injectivity and induced adjacency are preserved. Because the labelling is surjective, the image of the relabelled map is exactly the original source image, so global strongness is not weakened or silently assumed.

**Response transport.** A labelled response is precomposed with the inverse target equivalence, giving an embedding of the original target type. Inducedness is reflected; the map extends the prescribed source embedding pointwise, not merely up to isomorphism.

**Global strongness.** The image of the transported target map equals that of the labelled target response. The strong predicate is therefore carried to the identical finite subset of the ambient graph.

**Boundary.** The theorem assumes `HasStrongExtensionProperty M`. This property is derivable from a fair responding strong chain by PR #17, but existence of such a chain has not been proved. Accordingly this is an implication, not a completed construction of the countable strong Fraïssé limit.

**Proof integrity.** The exact statement was compiled in [run 38062233519](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38062233519), with the standard axiom audit and placeholder check. These reviews are separate adversarial checks performed by one assistant, not independently spawned referees.


## Fresh labels for finite successor stages — adversarial audit

**Old-map preservation.** Every vertex in the image of f receives exactly the old label of its unique preimage. The preimage is unique because f is injective.

**Freshness.** Every vertex outside the image of f receives a label strictly greater than the finite supremum of all old labels, avoiding accidental old/new identifications even if the old labels have gaps.

**Distinct new vertices.** Different new vertices have different Fin-card encodings; adding the same offset preserves distinctness. Thus the new labelling is injective provided the old labelling is injective.

**Empty base.** If A is empty, the supremum is zero and all B vertices receive distinct positive labels. No nonemptiness assumption is silently needed.

**Scope.** This is a carrier embedding theorem, not a construction of the adjacency relation on the new stage, nor a guarantee of realizing any scheduled graph extension.

**Kernel and diagnostic checks.** The [160-declaration run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38062409525) passed with standard axioms. The independent finite Python regression tests preservation and freshness; it does not replace the Lean proof. These are separate adversarial review perspectives by the same assistant, not independent external referees.


## Adversarial checks: finite Nat graph transport and coverage

**Adjacency and nonedges.** `transportedToNat` reflects adjacency on the labelled image because labels are injective. Thus induced nonedges are preserved, not merely edges. Dropping injectivity would invalidate the claim.

**Predimension.** Both finite vertex cardinalities and unordered induced-edge counts transfer along the injective induced map, and hence finite strongness and 2-sparsity are preserved.

**Old-vertex coherence.** `transportedToNat_agree_on_old` establishes old-old adjacency agreement under one finite stage extension. It does not construct a coherent infinite union or establish fair local responses.

**Coverage obstruction.** When A is empty and B is a singleton, `extendNatLabels` assigns the B vertex label 1 (empty old supremum 0, fresh offset 1, ordinal value 0). Every later fresh vertex lies above all existing labels. Thus label 0 can never enter an iterated chain of these extensions, whereas `Predimension.StrongChain` on ℕ requires every natural number to enter some stage. Any gaps created later are similarly permanent.

**Genericity negative control.** Leaving unused natural numbers isolated does not repair the extension property. An unused isolated vertex is a globally strong singleton base but has no edge to any vertex, so a legitimate one-edge strong extension of that singleton cannot be realized. Fix by constructing stages as consecutive initial segments of unbounded size, or by transporting the direct limit of genuinely used vertices to ℕ after its construction.

**Referee provenance.** These are distinct adversarial verification perspectives assessed by one assistant; no independently spawned external referee panel was available. Lean audits certify the finite statements, not the limit construction.


## Adversarial review: initial-segment carrier extension

**Old vertex labels.** The inverse of the tagged split sends `f(a)`
back to the old component `Sum.inl a`. The finite-sum equivalence embeds
that component without changing its natural value, and the cardinality
cast likewise preserves its natural value.

**No duplicates or gaps.** The carrier map is a composition of genuine
bijections, ending in `Fin (card B)`. Thus no two vertices share a label
and every natural number strictly below `card B` occurs exactly once.

**Empty source / smallest counterexample.** For an empty source and a
singleton target, the new map must have image `{0}`, unlike the old
maximum-plus-one construction whose image is `{1}`.

**Strongness and genericity boundary.** This is purely a relabelling
lemma. Once transported along induced graph embeddings, it preserves
finite predimension and strongness, but it does not produce a strong
amalgam, an unbounded chain, coherent limit graph, or responses to the
fair request schedule. Those remain independent theorem obligations.

**Provenance.** These are adversarial checks of separate possible failure
modes within the same review, not independently spawned referee agents.


## Adversarial review: finite fair strong response

**Base inducedness.** The source adjacency comparison is reversed and
then composed with the labelled diagram's inducedness proof. This
checks both edges and nonedges. Merely assuming an injective source
map would be insufficient for free graph amalgamation.

**Self-sufficiency.** The source is strong in the current stage and in
the target diagram; these are different hypotheses and both are used
to preserve two-sparsity of the amalgam.

**Identifications.** The normalized tagged amalgam has disjoint tails.
Equality of an old-stage image and a target image implies that they
arise from the same source vertex; no accidental tail identifications
are allowed.

**Strong images.** Both the current stage and the requested target
remain strong in the finite amalgam. This is needed to iterate the
construction and pass strongness to the eventual limit.

**Scope / negative control.** If source self-sufficiency is removed,
two K5 graphs joined over a K3 can have predimension -3, so even
two-sparsity may fail. This theorem neither guarantees growth of the
finite carrier nor constructs the countable chain.

**Provenance.** These adversarial checks were performed as separate
mathematical perspectives in the current review, not by externally
spawned human referees. The Lean CI and axiom audit are the machine
verification of the exact statement.


## Adversarial review: forced finite-stage growth

**Singleton sparsity.** No two-element set can be an edge in the graph
whose adjacency predicate is always false. Its predimension is therefore
`2 * card`, nonnegative on every subset, including the empty set.

**Empty-base strongness.** Both factors of the proposed joint embedding
are two-sparse. The empty induced graph is strong in each factor; this
would be false without subset-wise two-sparsity.

**Freshness.** The full tagged amalgam reports that any identification
of its factor images comes from the common base. Since the base is
`Empty`, the new singleton is provably outside the old-stage image.

**Inducedness and strength.** The old factor maps preserve and reflect
adjacency and have self-sufficient image in the new two-sparse graph.
A weak embedding or mere preservation of old edges would not be enough
to iterate the strong-age construction.

**Boundary.** Strict finite growth does not imply that stages cover
all ℕ until they are re-labelled coherently as consecutive initial
segments. Nor does it imply realization of any pending request.
These are separate adversarial checks in this review, not independently
spawned external referees.

## Adversarial review: coherent graph union

**Nonedges.** The one-step invariant is a bi-implication, not just
preservation of edges. Otherwise a new edge could appear between two
previously old nonadjacent vertices and invalidate induced copies.

**Support.** Every stage edge is required to have both endpoints in
its finite support; this makes edge relations monotone when combined
with old-old coherence. Omitting support would invalidate `edge_mono`.

**Comparison stages.** If an edge is witnessed at stage m but its
endpoints belong to earlier stage n, pass to max(n,m). Edge monotonicity
moves the witness forward and exact old-old agreement moves its
adjacency back to n. This proves *reflection* from the union.

**Carrier coverage.** The structure separately requires that every
natural number enter some stage, preventing the permanent gap exhibited
by the old `extendNatLabels` function.

**Scope.** The graph union theorem does not assert strongness of
successor stages, fair responses, or the existence of coherent stages.
These are the next construction obligations. The checks are separate
adversarial perspectives by one reviewer, not external agents.

## Adversarial review: finite induced adjacency transfer

**Edge enumeration.** A two-element edge is characterized by an unordered
finite set together with witnessed adjacent endpoints. Exact agreement
of adjacency on the finite domain transfers both inclusion and the
witness, in both directions.

**Predimension.** The vertex cardinality is unchanged, and the two
finite induced edge sets coincide. Thus
`2 * card(vertices) - card(edges)` is identical in both graphs.

**Intermediate sets.** Relative strongness requires comparing
predimension on every intermediate finite `C` with `A ⊆ C ⊆ B`.
The adjacency agreement is restricted separately to each such `C`,
not only to the two endpoints `A` and `B`.

**Negative control.** If graph predicates agree only on edges of A but
differ on edges involving B minus A, strongness need not transfer.
The theorem explicitly assumes induced agreement throughout B.

**Boundary.** The result is a graph-interface lemma. It does not prove
existence of an increasing finite chain, compatibility of its labels,
or the Fraïssé extension property. These are hostile proof checks by
the same assistant, not external referees.

## Integrated adversarial cross-check

The strict-growth theorem prevents a fair response with no new vertices from stalling the carrier. The exact old-old nonedge invariant prevents the union graph from changing an induced finite stage. The localized predimension/strongness transport bridges finite stages to the union. These are three logically different obligations. They do not, even together, imply the existence of a coherent fair response schedule. The present review uses independent mathematical failure modes and Lean kernel checks, not externally spawned referee agents.


## Adversarial review: strongness in the countable graph union

**Change of graph.** A finite strong inclusion A≤B is initially
computed in the successor *stage graph*. By exact induced agreement
on B, the localized predimension-transfer theorem moves that same
inequality to the limit graph. Strongness may not be transported
without reflection of nonedges.

**Global strongness.** The StrongChain theorem proves that each finite
stage is strong against arbitrary finite subsets of the union, by
embedding each test set in a later finite stage. No global limit
strongness is assumed before invoking the theorem.

**Two-sparsity.** Every finite vertex set is contained in a finite
stage. Its induced edge set in the limit equals that in the stage;
nonnegative predimension follows there. This conclusion quantifies
over finite subsets of ℕ; it does not invoke nonexistent Finset.univ
for an infinite vertex type.

**Missing existence.** The coherent system, stage growth, and the
local responses must still be recursively assembled. Neither
HasStrongSteps nor HasTwoSparseStages follows from coherence alone.

**Referee provenance.** These checks isolate different failure modes
but were carried out within one assistant review; no external
independent referee panel was spawned.


## Adversarial review: initial-segment exhaustion

**Progress.** Strict inequalities `size n < size (n+1)` imply by
induction `n ≤ size n`, regardless of the first size. No unstated
strict inequality at stage zero is used.

**Coverage.** For vertex x choose stage x+1; then
`x < x+1 ≤ size (x+1)`. This proves actual coverage of all ℕ,
not merely unboundedly many stage indices.

**Gaps.** The conclusion uses domains *exactly* equal to
`range (size n)`. It would fail for arbitrary finite subsets of ℕ
with growing cardinality but persistent holes.

**Boundary.** Constructing the stages, proving each finite strong
extension exists, and verifying fair responses remain separate.
These are adversarial mathematical perspectives, not external reviewers.


## Adversarial review: gap-free graph stage transport

**Old labels.** The carrier equivalence extends the prescribed
old equivalence pointwise. Its values, and hence numeric labels,
are unchanged on the image of the old finite embedding.

**No holes.** Since the new labelling is a bijection with Fin(card B),
the exact support image is range(card B). The empty-source case
assigns the first added vertex label zero, not one.

**Inducedness.** Graph transport uses an injective label and proves a
bi-implication on adjacency, including preservation of nonedges.

**Predimension and strongness.** Both finite vertex and unordered
edge counts are unchanged under transport. Strongness is transported
from A≤B to the corresponding consecutive old and new Nat domains,
not inferred merely from sparsity.

**Scope.** The theorem describes one chosen finite strong extension;
it does not ensure a fair response, strictly positive growth or
compatibility of an entire infinite sequence. Those properties must
be supplied by the subsequent recursive stage selection. This is
a same-assistant adversarial check, not an external referee panel.


## Adversarial review: stage response transfer to countable limit

**Applicability.** The source image is included in the current finite
support by the strongness hypothesis in AppliesAt. Thus both its
adjacency and self-sufficiency can be transferred to the stage graph
without assuming global graph equality.

**Answer.** A finite response has target image strong in the next
finite support. This includes all target vertices, so the same exact
induced comparison transfers target nonedges and the strong image
to the limit graph.

**Direction of strongness transport.** Applicability goes from limit
to stage; response goes from stage to limit. Reversing either
direction would leave a gap in the finite-to-countable argument.

**Fairness.** Only the already-verified schedule lemma and
`strongExtensionProperty_of_fairResponses` provide the extension
property. The new theorem supplies their local stage hypotheses,
not a construction of any of the stages.

**Scope and provenance.** No countable generic graph is constructed;
we check independent failure modes within the same review rather
than claiming independently spawned external referees.


## Adversarial review: general old-label graph coherence

**Injectivity.** Both old and new numerical labellings are assumed
injective. Otherwise reflection of adjacency under transport can
fail because two original vertices acquire one image.

**Exact old-label agreement.** The equality `new(i(a)) = old(a)`
is pointwise, not merely equality of the cardinalities or the
labelled images. This prevents swapping old vertex labels.

**Induced graph embedding.** The source/target graph assumption
preserves and reflects edges, hence ensures that the transported
graphs agree on old-old nonedges too.

**No carrier growth assumption.** The result works for arbitrary
injective Nat labellings. The separate initial-segment theorem
provides gap-free carrier coverage in the intended construction.

**Boundary.** This is an interface lemma; existence of a coherent
fair responding countable sequence is not inferred. These are
distinct hostile mathematical checks by the same assistant.

## Adversarial review: composition of strong images

**Intermediate strongness.** The original image f(A) is self-sufficient
in B, not necessarily in the final graph C. The second embedding must
have induced strong image in C; without its self-sufficiency the
conclusion can fail.

**Transport.** Strongness of f(A) in B transfers to g[f(A)] inside
g[B] using induced edge **and nonedge** preservation and injectivity
of g. Transitivity then gives self-sufficiency in C.

**Image identity.** The nested image (f[A]).image g equals the image
of the literal composite g ∘ f, so the theorem preserves the exact
source map, not only an isomorphic substructure.

**Scope.** No finite two-sparsity hypothesis is required for this
abstract relative-strongness calculation; the concrete C0 construction
has separate sparsity obligations. This is a same-assistant adversarial
check, with Lean certification still pending.

## Adversarial review: finite Nat stage pullback

**Carrier.** Every element of `Fin m` has numeric value below m,
and every number below m determines a unique element of `Fin m`.
The full finite-carrier image is precisely `range m`, with no holes.

**Inducedness.** The pullback graph's adjacency predicate is
definitionally the Nat graph evaluated on the two numeric images.
It preserves and reflects edges and nonedges.

**Predimension.** The existing induced-image theorem compares every
finite subset, not only the full stage, which is essential for
two-sparsity and self-sufficiency.

**Scope.** Strongness is relative to `range m`, not the whole Nat
graph; global strongness requires the separate countable-strong-chain
argument. These are distinct adversarial checks by one assistant,
not independently spawned referee agents.


## Integrated hostile checks

These proofs represent three logically distinct safeguards. Pointwise fixed old labels prevent accidental renumbering; exact induced adjacency prevents a later stage from adding old-old edges; transitivity of strong embeddings ensures the answered target remains strong after the forced-growth extension. The finite carrier pullback covers all intermediate subsets, not only whole stages. None establishes that a fair responding coherent chain exists. The checks were independent mathematical failure-mode perspectives within the same assistant review, not separate human referee certifications.


## Adversarial checks: finite response plus strict growth

**Two successive extensions.** It is insufficient to prove that the
first amalgam realizes the target and that a second graph grows: both
old and target embeddings must remain strong after the second step.
The lemma explicitly composes two induced strong embeddings.

**Identification.** The first tagged amalgam identifies the factors
only over their prescribed common base. Injectivity of the growth
embedding transports this exact identification condition to the
final carrier.

**Freshness.** The new vertex is outside the image of the entire
first amalgam. The image of the old stage lies within that amalgam
image; hence the new vertex cannot have been previously numbered.
No assumption that the request adds a vertex is required.

**Coherence.** The output embeds the old graph inducedly and fixes
the prescribed request base pointwise. However, this alone does not
give a Nat-labelled stage: separate initial-segment transport and
the old-label coherence theorem are still required.

**Scope and provenance.** No recursively constructed coherent fair
sequence is claimed; the theorem is an existential finite successor
statement. These are adversarial mathematical perspectives in the
same assistant review, not independently spawned external referees.

## Adversarial review: applicable Nat request to finite carrier

**Bounded range.** Applicability includes that the source-image
substructure is contained in the old stage. On `range n` this
is equivalent to each numerical source value being below `n`.
Without it the source cannot be interpreted as `Fin n`.

**Exact map.** The finite source map has the *same numerical values*
as the scheduled Nat map, not merely an isomorphic image. This is
needed to answer the original request pointwise.

**Inducedness.** The finite stage pullback reflects nonedges as well
as preserving edges. A weak graph homomorphism is not sufficient.

**Strongness.** The source is strong only relative to the current
stage, not yet globally. The pullback uses strongness on every
intermediate finite subgraph, preserving the exact hypothesis needed
for tagged strong free amalgamation.

**Boundary and provenance.** This supplies finite input data for
one scheduled request, not a coherent recursive chain. The review
separates distinct proof obligations but is not a separately spawned
external panel.

## Adversarial review: canonical Fin labels

**Identity, not arbitrary permutation.** An abstract bijection from
`Fin n` to its cardinal representative could reorder old vertices.
The canonical cast identifies the equal cardinalities without
changing their numeric values.

**Stage zero.** The cast on `Fin 0` is valid vacuously; no extra
nonempty-carrier assumption enters the recursive initialization.

**Scope.** Numeric labelling is independent of graph adjacency and
strongness. This only supplies the old labelling parameter required
by the finite graph transport theorem, not an actual countable chain.
The checks are separate adversarial proof perspectives within one
assistant review, not an external referee panel.

## Adversarial review: trivial strong request

**Empty structure.** There are no vertices or edges on `Fin 0`;
its two-sparsity is vacuous. The empty inclusion is strong in itself,
and the unique map into Nat is injective and induced.

**Base self-sufficiency.** In any two-sparse finite stage, the empty
subset has predimension zero and is strong. Without two-sparsity
this application could fail.

**Scheduling.** A growth-only fallback is permitted only if no
applicable request is scheduled. Otherwise responding to the empty
diagram would not establish the fair response property.

**Scope.** This lemma provides one elementary witness, not a
recursion, coherent stage construction, or genericity theorem.
These independent failure-mode checks were performed by one
assistant and are not external human referees.


## Integrated adversarial cross-check of successor prerequisites

The four proof obligations are not interchangeable. A fair request that is applicable needs its original source Nat map preserved pointwise. The intermediate finite amalgam must retain both induced nonedges and strong embeddings; strict growth must occur regardless of whether the response adds vertices. Initial-segment casts must preserve old numerical labels, and growth-only fallbacks may only replace requests that do not apply. The individual adversarial perspectives identify these failure modes, but are not independent external referee certification. The consolidated Lean build and standard-axiom audit are required before certification.


### Equality-decider adversarial finding (composite finite response)

A Lean theorem's type may depend on the selected `DecidableEq`
through a noncomputably defined finite induced-edge set. A
`GraphOn.toPredimension` built with the structural Sum decider is
not definitionally identical to one built with a new local
`Classical.propDecidable`. The earlier growing-response attempt
silently changed this instance during composition of strong
embeddings. The repair fixes explicit structural instances on
both tagged carriers, and the proof reuses them. This must be
verified by an exact theorem-type/axiom audit, not by an
independent finite-model regression alone. This review is one
assistant's separate adversarial perspective, not an external
human referee result.


## Adversarial review: recursive fair Fraisse stage choice

**Existence is not hidden.** The proof takes exactly
`∀ k s, ∃ t, IsFairStrongSuccessor k s t` as a hypothesis.
Each `Classical.choose` is applied to that finite existential witness.
No generic countable graph or prior fair chain is postulated.

**Coverage.** The stage domain is `range(size k)` and every
`size k < size(k+1)`; these two properties together prove the union
is all Nat. Merely increasing the number of vertices in arbitrary
subsets would not suffice.

**Induced graphs.** Exact agreement, not only forward edge
preservation, is part of `IsFairStrongSuccessor`. Thus the limit
does not add edges among already present vertices and all finite
stage strongness calculations transfer.

**Fairness.** The successor responds to every request decoded at
stage k *if it applies then*. No response obligation is imposed
on a request with an invalid, noninduced, nonstrong or unavailable
source map. Repeated scheduling subsequently realizes a request
once its globally strong source lies in a finite stage.

**Strength.** Each finite stage is two-sparse on its own support,
while each successor is a strong extension in the new stage graph.
The verified strong-chain theorem, not an extra implicit genericity
assumption, supplies global strongness in the union.

**Remaining exact task.** Construct the finite one-step witness
for every input stage and schedule index using the growing-response
lemma for applicable requests and the trivial empty request otherwise,
then label the new carrier by an initial segment and preserve the
old numerical labels. This review checks distinct mathematical
failure modes within one assistant; it is not an independent external
referee panel.


## Adversarial review: concrete Nat growing response

**Two-sparsity and strongness.** The source restriction is strong
relative to the old finite stage, the response and forced-growth
amalgams are strong, and graph transport to the new consecutive range
preserves every intermediate predimension. Without all three, the
new stage could fail to be in the class.

**Numerical freshness.** The growth step produces a vertex outside
the old image. Under the new bijection to a finite initial segment,
if its number were below n it would coincide with a numbered old
vertex. Thus the successor's stage size is strictly larger than n.

**Induced coherence.** Each pair of old vertices retains its numeric
labels. The graph transport preserves and reflects adjacency, so
a previously absent old-old edge cannot appear at a successor.

**Pointwise response.** The answer map into the Nat carrier is the
composite of the finite answer embedding and the new numbering.
The amalgam agreement on the labelled source together with the
old numbering proves equality with the original request map, not
merely equality of ranges or graph types.

**Target strength.** The target is strong in the finite grown graph.
Transport under the new numerical embedding gives a strong
substructure inside the full next Nat range; this is stronger than
merely obtaining an induced copy of the target.

**Remaining gap.** This is a *finite* existential successor lemma
in the applicable case. A recursive stage selection, handling of
nonapplicable requests, and countable limit assembly are still
outstanding. These are independent adversarial mathematical
perspectives by the same assistant, not a spawned panel of
external referees.

## Adversarial review: recursive fair Fraisse stage choice

**Existence is not hidden.** The proof takes exactly
`∀ k s, ∃ t, IsFairStrongSuccessor k s t` as a hypothesis.
Each `Classical.choose` is applied to that finite existential witness.
No generic countable graph or prior fair chain is postulated.

**Coverage.** The stage domain is `range(size k)` and every
`size k < size(k+1)`; these two properties together prove the union
is all Nat. Merely increasing the number of vertices in arbitrary
subsets would not suffice.

**Induced graphs.** Exact agreement, not only forward edge
preservation, is part of `IsFairStrongSuccessor`. Thus the limit
does not add edges among already present vertices and all finite
stage strongness calculations transfer.

**Fairness.** The successor responds to every request decoded at
stage k *if it applies then*. No response obligation is imposed
on a request with an invalid, noninduced, nonstrong or unavailable
source map. Repeated scheduling subsequently realizes a request
once its globally strong source lies in a finite stage.

**Strength.** Each finite stage is two-sparse on its own support,
while each successor is a strong extension in the new stage graph.
The verified strong-chain theorem, not an extra implicit genericity
assumption, supplies global strongness in the union.

**Remaining exact task.** Construct the finite one-step witness
for every input stage and schedule index using the growing-response
lemma for applicable requests and the trivial empty request otherwise,
then label the new carrier by an initial segment and preserve the
old numerical labels. This review checks distinct mathematical
failure modes within one assistant; it is not an independent external
referee panel.

## Adversarial review: proposed full finite-to-generic construction

**Scheduling.** At every stage k, an applicable scheduled request
is acted on, not replaced by the empty fallback. Inapplicable
and undecodable requests impose no response obligation at that
stage. Repetition of every request beyond every index is essential
for realizing bases which only appear later.

**Forced growth.** Both branches call a strictly growing finite
response. Thus the sequence of gap-free stage sizes tends to infinity
and covers all natural numbers, even when every scheduled request
is empty, invalid or already realized.

**Strongness and inducedness.** Both branches yield a two-sparse
successor with the previous interval self-sufficient. Pointwise
old-label preservation plus reflection of nonedges gives a
coherent induced limit; the strong-chain theorem then gives
global strongness of each stage.

**Choice.** Classical case distinction concerns only applicability,
and each successor is selected from a separately proved finite
existential theorem. No previously existing M0 or genericity is
assumed. The repeated fair schedule then supplies the extension
property by a previously verified implication.

**Scope and verification.** The finished source would establish
the existence of one countable two-sparse graph with the full
labelled strong extension property. It would not by itself prove
all manuscript Ramsey or Ellentuck theorems, nor equality with
algebraic closure. The new Lean endpoint has not yet passed CI;
this is a mathematical failure-mode review by the same assistant,
not a spawned external referee panel.


### Computational adversarial reviewer: growing responses

An independently implemented edge-set and subset-enumeration checker
tried every compatible labelled strong pair of finite graphs on
at most three vertices, with all source injections of size at most
two. It tested the literal numerical labels and all intermediate
predimension inequalities after performing request amalgamation and
forced growth. No counterexample occurred in 2,337 applicable
diagrams. As a negative control, dropping self-sufficiency of the
common K3 causes the free join of two K5s to violate 2-sparsity.
This is independent *code* in the same review, not an independent
human or Lean referee and not a substitute for the pending axiom audit.

**Consolidated integration status:** all three theorem layers are pending the combined Lean CI and standard-axiom/placeholder audit. The finite tests are diagnostic only. The strong genericity endpoint is not yet certified, and no manuscript marker should be upgraded until the exact source revision has passed.

**Reconciled integration status:** this branch starts from main after the certified 207-declaration fair-recursion theorem (PR #45); it does not duplicate that module. The concrete strong genericity claims remain **pending a complete integrated Lean build and axiom audit**. The external combinatorial results and the manuscript's big Ramsey/Ellentuck conclusions are not derived here.


## Adversarial review: strong age of the constructed generic

**Vacuous source versus genuine target.** Universality is obtained by
extending an empty induced embedding into an arbitrary valid finite
two-sparse target. It does not merely assert that the target can be
embedded as an ordinary induced graph; the image is globally strong.

**Ambient hypotheses.** Both exact premises of the conditional theorem
have independent Lean proofs for the concrete `genericTwoSparseGraph`:
nonnegative predimension on every finite subset, and the strong
extension property. Neither is postulated as a field of a new object.

**Arbitrary finite labels.** The source theorem already transfers
from labelled strong diagrams to arbitrary finite carrier types.
The corollary cannot substitute an arbitrary enumeration without
preserving the actual induced adjacency and strength.

**Global, not local.** The target image is strong against every
finite set in the ambient graph, rather than only against the finite
stage where it first appeared.

**Scope.** Strong universality alone does not imply strong
ultrahomogeneity, uniqueness or any of the paper's Ramsey properties.
The remaining back-and-forth is recorded separately. These are
five adversarial failure-mode perspectives by one assistant, not
independently spawned external referees.


## Adversarial review: finite strong forth extension

**Source container.** Arbitrarily adjoining a vertex to a strong
finite domain need not give a strong set. The proof uses the explicit
finite-strong-cover property to select c strong in the full source
graph and containing the requested vertex.

**Base strength.** Global self-sufficiency of a implies a≤c. This
is verified in the induced graph on the finite subtype of c using
the previously proved exact predimension transport; it is not
inferred from graph inclusion alone.

**Target strength.** The arbitrary finite strong extension theorem
returns a globally strong image of c in N, rather than a copy that
is strong only within some selected finite target stage.

**Exact original map.** The old partial isomorphism is an equivalence
of induced finite subtype carriers. The resulting map g on c agrees
pointwise with p after the canonical inclusion a→c. Adjacency is
preserved and reflected, including nonedges.

**Finiteness and proof scope.** The carrier c is finite, no uniform
closure size is assumed, and neither the back step nor the
alternating bijection has been claimed. These mathematical adversarial
perspectives are all carried out by one assistant and are not
independently spawned human referees.


## Adversarial review: strong back extension

**Symmetry.** The proof uses the inverse equivalence and exchanges
the two ambient graphs, rather than assuming that a forward
extension automatically covers the opposite range.

**Exact values.** The inverse partial map sends each original
target vertex to its original source vertex. It is preserved
pointwise after inclusion in the larger target domain.

**Induced nonedges.** The equivalence reverses the biconditional
for adjacency and reflects nonedges as well as edges.

**Strongness on both sides.** The enlarged target range is
globally strong by the finite strong-cover premise; its new image
in the source graph is globally strong by the extension property.

**Scope.** Back-and-forth still needs coherent alternating finite
partial maps and a proof that their union is a bijective induced
graph isomorphism. This review tests five logically independent
failure modes within one assistant, not an external referee panel.

**Integrated audit:** the complete source for forth and back has passed [GitHub Actions run 38112788714](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38112788714), checking 215 Lean declarations with only standard logical axioms, scanning 47 Lean files for placeholders and passing the finite regression suite. The reconciliation on newer main requires its own green CI before merging.


## Adversarial review: finite strong closure of the generic

**Global versus relative strength.** Each finite stage is
globally strong in the constructed graph by the strong-exhaustion
theorem, not merely strong relative to the next finite stage.
The closure is taken inside such a globally strong container.

**Least hull independence.** The definition selects one finite
container using classical choice, but the result is contained
in every other finite globally strong container. Thus the
closure is intrinsic and does not depend on the enumeration or
the chosen stage.

**Finite cardinality.** Every closure is represented as a
`Finset ℕ`; no uniform numerical bound on its size is claimed.

**Back-and-forth utility.** When extending a finite strong
partial isomorphism to include one additional vertex, enlarge
the finite domain to its strong closure first. Otherwise
global strength can be lost.

**Scope and provenance.** The closure as a predimension hull is
not yet the manuscript's entire named functional expansion,
nor does the lemma establish homogeneity. These five
adversarial failure-mode perspectives come from one assistant
review, not an independent external panel.

**Audit update:** the source proof passed [Lean run 38112434522](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38112434522), checking 219 declarations using only standard logical axioms and 46 files for placeholders. This reconciled branch must pass its own CI before the merged result is certified.

## Adversarial review: finite image normalization

**No lost or invented vertices.** The subtype carrier is defined
by membership in the literal finite image of f. The two inverse
laws show that all and only those image vertices occur.

**Injectivity is essential.** Without f being one-to-one, the
construction cannot be an equivalence and could collapse distinct
vertices in a strong partial map.

**Exact old values.** The forward equivalence sends a to f(a)
on the nose, rather than through a freely chosen permutation of
the image carrier.

**Finite carrier boundary.** The result depends on the finite
source type, not on any global finiteness of the target carrier,
so it applies equally to finite strong subsets of ℕ.

**Proof scope.** This is representation infrastructure. Its use
to extend partial isomorphisms and carry out back-and-forth must
still be verified separately. These checks are mathematical
adversarial perspectives of one assistant, not independent
external referees.

**Verified source runs:** generic closures passed [38112434522](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38112434522) (219 standard-axiom declarations; 46 placeholder-free files), and exact image equivalences passed [38113224922](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38113224922) (217 declarations; 48 files). Their combination with newer main and the merged finite forth/back proofs requires a fresh integrated CI.


## Adversarial integration review: strong back-and-forth core

**Finite domains:** source and target of each partial map are
literal finite subsets of ℕ, globally strong in their own graph.

**Preservation:** each extension retains all old numerical
values and reflects edges and nonedges.

**Two-sided coverage:** source and target domains each exhaust
ℕ; source coverage alone cannot yield surjectivity.

**Carrier normalization:** finite injective responses are
identified with their exact finite image; no arbitrary
finite enumeration can permute old labels.

**Axiom boundary:** the union and recursive construction
consume an explicit finite joint-step existence hypothesis.
No genericity or isomorphism is postulated as that hypothesis.
It must be discharged by composing actual finite strong
forth/back steps. These separate failure-mode audits are
performed by the same assistant, not independently spawned
human referees.


## Adversarial review: finite joint strong extension

**Non-circularity.** The only inputs are two-sparsity on every
finite set, finite globally strong covers and the finite strong
extension property in both graphs. Neither a countable
isomorphism nor the joint-step premise is assumed.

**Exact carried values.** A finite strong response is normalized
to its literal image before being treated as a partial
isomorphism. The old map is preserved pointwise; arbitrary
finite enumeration would not suffice.

**Reverse direction.** The second step applies the forth
extension lemma to the inverse partial isomorphism, and
`Extends.inverse` transports the extension order back.
Keeping only the source domain would not ensure target coverage.

**Global strength.** Both finite domains remain globally
self-sufficient, and the passage from a chosen finite container
to its image is justified by exact induced strong embeddings.

**No old-old nonedges added.** Each finite partial equivalence
preserves and reflects adjacency; the union theorem compares
each pair at a common later stage. Thus the limiting bijection
is an induced graph isomorphism.

**Scope.** The stronger homogeneity theorem requires additionally
showing that the alternating back-and-forth union extends a
specified *initial* finite strong map, not just the empty map.
These are adversarial mathematical checks by one assistant, not
independently spawned external referees.


## Adversarial review: strong homogeneity and uniqueness

**Prescribed initial values.** A back-and-forth starting with a
nonempty finite strong partial isomorphism must retain its
values at stage zero. This is verified by the stage-independent
union evaluation theorem, rather than inferred from abstract
existence of a global bijection.

**Two-sided surjectivity.** The joint-step construction grows both
source and target domains at every step. A one-sided exhaustion
would not establish an automorphism.

**Global strongness.** The initial finite partial map and all
successor partial maps require self-sufficiency against the
entire ambient graph, not only their containing finite stage.

**Inducedness.** The total equivalence preserves and reflects
nonedges as well as edges by eventual common-stage agreement.

**No circular assumptions.** The finite joint-step theorem,
if fully verified, consumes only two-sparsity, finite strong
covers and strong extension property in each graph. The countable
Fraïssé limit and its uniqueness are not assumed.

**Separate scope.** Theorem-level strong homogeneity identifies
the constructed graph with the pure strong Fraïssé limit.
The functionally expanded closure presentations, the big
Ramsey-degree results, and Ellentuck-space axioms still require
independent proofs. This is one assistant's adversarial review,
not independently spawned external referees.


## Adversarial review: free copies avoiding a finite container

**Referee A — actual overlap.** The two tagged factors are embedded
strongly over the literal common base (C). The no-unintended-
identifications theorem guarantees that a point of (D\setminus C)
cannot be identified with a point of the old (B).

**Referee B — old labels.** The ambient strong extension property
is applied with the induced finite subtype of the *actual* (B)
as its base, using the inclusion into (M_0). The resulting
embedding fixes every vertex in (B) pointwise rather than
merely mapping it to an isomorphic copy.

**Referee C — relative to global strength.** The new (D)-factor
is strong in the finite tagged amalgam, and the amalgam's image
is globally strong in (M_0). Transitivity is needed to make
the image of (D) globally strong.

**Referee D — induced nonedges.** Both factor embeddings are
induced. The new image must reflect nonedges, since a mere
graph homomorphism is insufficient for later extension of
the isomorphism to an automorphism.

**Referee E — iteration/acl boundary.** A single avoiding copy
does not itself prove an infinite orbit. The iteration must
enlarge the finite strong container to include the previously
constructed images, and homogeneity must transport a distinguished
vertex of (D) to the new images. First-order algebraic closure
requires a final semantic argument.

These checks isolate five mathematical failure modes within
one assistant review and are not independent external referees.


## Adversarial review: arbitrary finite avoidance for strong copies

**Container existence.** The actual generic has a finite globally
strong cover property for every finite set. The chosen container
contains the base and the entire forbidden set, not merely the base.

**Forbidden set need not be strong.** The input (F) is arbitrary
finite; only the enlarged (B) needs to be globally strong.
This distinction is essential for arbitrary lists of previously
constructed conjugates.

**Old base fixed literally.** The strong copy agrees pointwise with
the original embedding of the base (C), not with a chosen
isomorphic copy.

**New vertices avoid all of F.** If a new image vertex belonged to
(F\subseteq B), the tagged-amalgam identification criterion
would force its source vertex to lie in the base, a contradiction.

**Scope.** Unbounded finite copy existence is sufficient to
iterate, but iteration and automorphism extension have not been
included in this theorem. These are same-assistant adversarial
failure-mode checks and not a panel of external human referees.


## Adversarial review: infinitely many strong conjugates

**Referee A — finite forbidden set.** For each finite (F),
the construction obtains a strong induced copy of the finite
closure of (C\cup\{a\}) whose nonbase vertices avoid all of
(F). It does not mistake a single avoiding copy for infinitely
many distinct copies.

**Referee B — actual automorphism.** The two finite induced
copies of (D) are both globally strong. The verified strong
homogeneity theorem extends the induced finite equivalence
to a total automorphism of the *actual* countable generic.

**Referee C — pointwise base agreement.** Both free amalgamation
and strong homogeneity preserve each vertex of (C), not merely
its image set. Hence the final automorphism belongs to the
pointwise stabilizer of (C) and of all generators (X\subseteq C).

**Referee D — distinguished vertex.** Since (a\notin C), its
representative in the finite closure (D) cannot belong to the
image of the base embedding. The avoidance theorem therefore
forces (e(a)\notin F).

**Referee E — finite invariant sets versus FOL.** Every solution
set of a finite algebraic formula over (X) is finite and
stabilizer-invariant, so the combinatorial theorem would
exclude any (a\notin\operatorname{cl}_s(X)). The converse
inclusion uses the separately developed induced-diagram
uniqueness lemma. The missing component for a *fully formal*
identification with acl is now the first-order interpretation
of finite diagram formulas and algebraic formulas.

These five independent mathematical failure-mode perspectives
were carried out in one assistant review rather than by
externally spawned referee agents.


## Adversarial review: strict closure and finite induced diagrams

**Referee A — predimension minimizer.** The finite family of
supersets of (X) inside (C) is nonempty. A minimum-(\delta)
member is strong *inside (C)*, since every intermediate superset
still belongs to the minimizing family. As (C) is globally
strong, transitivity makes the minimizer globally strong.

**Referee B — leastness is essential.** The minimum must equal
the least globally strong (C). Equality of (\delta(D))
and (\delta(C)) for a proper intermediate (D) would make
(D) strong and contradict leastness. A nonminimal strong
container invalidates this assertion; the edgeless two-vertex
negative control checks that failure mode.

**Referee C — competing finite image.** For any (B\supseteq X)
of equal predimension, submodularity on (C,B), together with
global strength of (C), forces (C\cap B=C). A copy of the
induced diagram has equal predimension and cardinality, and
hence precisely the same vertex set. Distinguish this conclusion
from the existence of a first-order formula expressing the diagram.

**Referee D — all finite subsets.** The Python regression
enumerates every labelled graph on up to five vertices and all
generating and competitor sets, not just strong induced subgraphs.
It verifies the strict inequality and both image-inclusion and
equal-cardinality conclusions.

**Referee E — model-theoretic boundary.** This finite argument
would show that the induced diagram of (C) over (X) admits
only finitely many realizations, once that diagram is expressed
as a first-order formula. The opposite inclusion requires
arbitrarily many disjoint strong realizations and extension to
automorphisms. Neither model-theoretic assertion is hidden in
the combinatorial theorem.

These are independent mathematical failure-mode perspectives
and an independent finite computation within the same assistant
review, not separately spawned external referee agents.

## Adversarial review: finite induced-copy image uniqueness

**Referee F — no hidden global strength of the competing copy.**
The alternative induced copy (f[C]) need not be globally strong.
The proof does not assume this: it uses induced adjacency,
the equal cardinality and predimension, the globally strong
original (C), and submodularity.

**Referee G — internal automorphisms.** The conclusion is equality
of image *sets*, not pointwise equality of the two embeddings.
A finite closure may admit permutations preserving the graph
and its generating tuple.

**Referee H — finiteness and formula semantics.** An induced map
between finite graph structures preserves all unordered edge
counts and reflects nonedges. Thus any first-order existential
formula listing the finite induced diagram has candidate vertices
only in (C). The Lean statement establishes the combinatorial
fact, not yet the first-order interpretation of that formula.

**Audit update (11 October 2026):** Original PR #69 passed CI [run 38153898725](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38153898725), auditing 260 declarations using standard logical axioms only and 59 placeholder-free Lean files, including the strict strong closure and finite induced-copy image theorems. The independent 1,100-graph regression also passed. This reconciled branch must pass a new integrated CI check before merging. The later merged PR #72 independently proves infinite automorphism orbits outside strong closure, but the first-order semantics of model-theoretic algebraic closure are still not formalized; do not upgrade `acl=cl_s`.


## Adversarial review: finite orbit vs finite strong closure

**Image versus pointwise fixation.** An automorphism fixing the
generators need not fix every element of their finite closure;
it only permutes the closure. The induced-diagram uniqueness
theorem proves equality of the *image set*, which suffices to
bound all automorphism images inside the finite closure.

**No global-strong-image assumption.** The restriction of the
ambient automorphism to the finite closure is induced and
injective, but the orbit argument does not separately assume
its image globally strong. It relies on the already audited
finite diagram uniqueness result.

**Infinite orbit exclusion.** A purported finite bound for the
orbit of a vertex outside the closure is refuted by the explicit
strong-conjugate avoidance theorem. This step uses pointwise
fixation of the *original* generator set, not the larger
closure alone.

**Parameter-free corner case.** The proof permits an empty
generator set; the same finite closure and orbit statements
apply without choosing any special vertex.

**Remaining first-order boundary.** Finiteness of an automorphism
orbit is not a general definition of model-theoretic algebraic
closure without extra hypotheses. The result explicitly avoids
that substitution. To establish acl=cl_s in the manuscript
one still needs first-order algebraic-formula semantics and the
finite induced closure-diagram formula.

All five are distinct mathematical failure-mode checks made
within one assistant review, not independently spawned referee
agents.


## C0 two-old-neighbour lemma: adversarial self-review (12 October 2026)

1. **Old-neighbour versus unordered-edge referee:** `oldNeighbours`
   counts distinct old vertices; `backEdges` counts unordered graph
   edges. The already proved injection/bijection of `C0Neighbours.lean`
   identifies the counts. Nothing assumes an orientation.
2. **Strongness referee:** the inequality requires the actual old prefix
   to be globally strong. No claim is made for an arbitrary induced
   finite prefix, where three old neighbours could occur.
3. **Minimal-choice referee:** equality two implies the closure of
   `a∪{x}` equals that one-point set. It implies the *whole increment*
   is singleton only after `equal_closure_of_minimal_choice` transports
   closure from the chosen generator `v` to `x`.
4. **Ambient referee:** the strong requirement `D` is finite and
   globally strong, and contains the old prefix; the chosen vertex is
   constrained by `IsMinimalChoice`. There is no assumption that `x`
   was the originally chosen generator.
5. **Scope referee:** the two new declarations do not certify the
   global block-enumeration schedule or any downstream Ramsey property.

All five are distinct proof-audit perspectives of this assistant,
not independent external referee agents. Both exact theorem endpoints passed
[Lean CI run 38237316769](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38237316769)
with 271 standard-axiom declarations and 64 files scanned for placeholders.


## Adversarial checks: finite C0 exhaustion runs (12 October 2026)

**Referee A — scope of strongness.**
`IsMinimalStrongStep a b` gives strongness in b, but its
every-generator lemma additionally requires b globally strong.
Otherwise equality with a closure in the **ambient** generic
would not follow from local minimality alone.

**Referee B — closure of a competing generator.**
Given x in b minus a, the closure of a union {x} is globally
strong, contained in b and strong in b. Local minimality
then forces that closure to equal either a or b; membership
of x excludes a. No predicate silently assumes x is the chosen
generator.

**Referee C — finite termination.**
The terminal set is the finite globally strong hull of a union
s. The pre-existing `finite_minimal_decomposition` is a
genuinely finite inductive chain, not an infinite run packaged
as a finiteness axiom.

**Referee D — arbitrary finite requests.**
The argument allows s to contain points outside a and points
already inside a. Strict growth is asserted only for the
separate one-vertex case x not in a. The empty-request and
already-present cases must not produce fictitious nonempty steps.

**Referee E — countable scheduling.**
It would be circular to infer existence of one exhausting
omega-sequence from the assertion that each finite request has
some finite completion run. The compatible concatenation/
scheduling theorem is therefore left as an explicit next
formalization obligation. No functional Fraisse property,
recurrent ordering, or big Ramsey consequence is inferred.

These are adversarial self-review perspectives; no independent
human or agent referees were spawned. Pending full Lean build,
standard-axiom audit, placeholder scan and finite regressions.


## Adversarial checks: strict C0 skeleton (12 October 2026)

**Referee A — genuine freshness.**
One cannot choose a fresh vertex from a bounded range. The proof
uses the pigeonhole inequality for the finite set a and the range
of length |a|+1. It does not assume an order-preserving enumeration.

**Referee B — avoidance of vacuous growth.**
A bare demand to insert n would allow an empty step if n already
belonged to the closure. The extra fresh vertex forces strict
inclusion and guarantees each finite minimal refinement has at
least one nontrivial step.

**Referee C — finite strong closure.**
The new stage is defined as the intrinsic closure in the actual
constructed countable graph, not as a hull in an arbitrary
finite carrier. Global strongness follows from the certified
strong exhaustion underlying M0.

**Referee D — exhaustive coverage.**
Vertex n is explicitly included at stage n+1, so every vertex
appears without a combinatorial compactness or diagonal fusion
assumption. The strong-chain coverage property uses this
specific bound.

**Referee E — minimal increments vs strong skeleton.**
The skeleton links are generally not minimal. A separate finite
minimal-chain proof refines each link; flattening those finite
chains to an omega-enumeration has not yet been formalized.
Therefore the construction is not claimed to certify the
full manuscript's minimal-component enumeration or unary
functional Fraisse structure.

These are deliberately separate self-checking perspectives, not
independently spawned external referees. Status pending the
integrated Lean and standard-axiom audit.


## Adversarial checks: finite C0 trace data (12 October 2026)

**Referee A — Prop/Type elimination.** A proof of
`MinimalStrongChain` is in Prop and has multiple constructors.
It is not legal to recursively compute a list directly from it.
The construction proves `Nonempty (MinimalStrongTrace ...)`
inside Prop and only then chooses a Type-valued witness.

**Referee B — minimality certificate.** The trace is not a bare
list of finite vertex sets; each step retains
`IsMinimalStrongStep`, and the independent `MinimalStepList`
predicate recovers the exact certificate on the recorded sources.

**Referee C — boundary duplication.** `starts` does not record
the final stage of a trace. Consequently successive lists for
`S_n → S_{n+1}` and `S_{n+1} → S_{n+2}` concatenate without
introducing the illicit zero-length step `S_{n+1} → S_{n+1}`.

**Referee D — nonempty intervals.** If `S_n=S_{n+1}`,
the trace might be reflexive and its source list empty.
The extra fresh vertex in the certified skeleton gives
`S_n ⊊ S_{n+1}`, explicitly excluding that case.

**Referee E — exact gap.** The existence of nonempty finite
trace lists and their finite append lemma is not itself a proof
that the infinite concatenation has order type omega, or that
its graph enumeration is functionally generic. The countable
prefix-indexing/gluing theorem remains a separate obligation.

These are five independent *questions* applied within one
assistant self-review, not independent external referees.
Full Lean build/axiom scan remains pending.


## Adversarial self-review of C0 block offset arithmetic

* **Coverage:** the prefix sum after n nonempty blocks is at least
  n; the least covering block exists for every natural position.
* **Lower boundary:** the chosen least covering block cannot start
  after the position (or its predecessor would already cover).
* **Uniqueness:** monotonicity of cumulative lengths excludes both
  an earlier and a later competing interval.
* **Freshness:** strictly positive lengths are necessary. The
  proof invokes the independently certified nonemptiness of
  every skeleton refinement; no zero-length dummy step is added.
* **Scope:** uniqueness of an arithmetic block index alone does
  not verify the structural successor relation between stages
  in distinct blocks, nor the unary closure presentation.

These are distinct adversarial verification passes performed
by this assistant, not external independent referee agents.


## Adversarial checks: indexed finite minimal traces (12 October 2026)

1. **Endpoint:** the nil/refl trace has length zero and the same
   source and target; its terminal accessor is its source.
2. **Succession:** the step case exposes the genuine initial
   minimal extension; the recursive tail has the correct source.
3. **No fictitious boundary step:** `at` defaults to the terminal
   for out-of-range inputs, but minimality is claimed only for
   `j < starts.length`, never at equality.
4. **Data/type:** induction is on the data-valued trace, not on
   a proposition-valued minimal chain; the latter was converted
   by a separate audited existence theorem.
5. **Scope:** this checks finite trace indexing, not the still
   missing global omega flattening, finite-order recurrence,
   or functional Ramsey theorem.

These are five distinct adversarial checking perspectives
within one assistant session, not independently spawned agents.


## Adversarial review: one countable C0 minimal enumeration

1. **Unique half-open indices.** Every natural position lies
   in precisely one block, and its local offset is bounded by
   the positive length of that block. Zero-length blocks are
   excluded by certified strict skeleton growth.
2. **Internal successors.** If the next position remains in
   the same finite trace, the existing indexed-trace theorem
   certifies the step, with no arbitrary re-choice of a trace.
3. **Boundary successors.** If the next position is exactly
   the block end, the last actual minimal step lands in the
   terminal skeleton stage, which is the next trace's source.
   No `S_{n+1} → S_{n+1}` stutter is inserted.
4. **Coverage.** Every skeleton stage occurs at an explicit
   cumulative offset. Consequently each vertex of M0 is in
   at least one flattened stage. Coverage is not inferred
   from strictness alone.
5. **Generated closure.** The final equal-closure statement
   assumes the new vertex is in the target but not the old
   stage, and uses global strongness of the target. It does
   not assume that new vertex was the temporary generator.
6. **Scope.** A countable minimal graph enumeration alone
   is not the same as the functional free-amalgamation
   Fraisse limit: the latter still needs its unary closure
   operations, local-form theorem, and extension schedule.

These are six separate hostile proof checks carried out
within one assistant review, not spawned independent agents.
CI is pending; no theorem is called certified on this note alone.


## Adversarial checks: empty initial C0 stage

1. The empty induced graph has predimension zero exactly,
   not merely nonnegative predimension.
2. The generic's finite two-sparsity is a proven theorem
   for **every finite subset** of the ambient countable graph.
3. Global strength of ∅ quantifies over all finite ambient
   containers and all intermediate finite subsets; it is
   not inferred solely from ∅ being strong at stage zero.
4. The global least-closure theorem identifies
   `genericStrongClosure ∅` with ∅; no arbitrary
   chosen finite strong container remains in the conclusion.
5. Coverage of the flattened enumeration uses the
   certified strong chain's actual `covers` witness,
   not a compactness or pointwise stabilization argument.

These are deliberately separate mathematical failure-mode
reviews by the same assistant, not independent spawned referees.


## Adversarial proof audit: dependency-closed block union

1. A union of whole components need not be strong; all back
   neighbours of the included component must already be selected.
2. The actual common vertex set is `a ∩ (x ∪ B) = x`;
   the disjointness hypothesis is indispensable to this equality.
3. Strongness is required of x in the **old graph a**, not
   merely strongness of a in the new ambient graph.
4. The no-cross free-amalgam lemma establishes strongness of
   `x ∪ B` inside `a ∪ (x ∪ B)`; rewriting the latter to
   `a ∪ B` uses x ⊆ a.
5. The global corollary needs the entire new prefix globally
   strong; it is not obtained from the local statement alone.
6. This proves one predimension induction step, not the
   global unary-closed-set characterization or functional age.

These are independent proof-checking perspectives of the
same assistant, not spawned external referee agents.


## Adversarial checks: C0 component partition

1. A₀=∅ is genuinely Lean-proved; an arbitrary strong
   exhaustion might have a nonempty initial stage.
2. Each step is strict, so the finite difference B_n is
   nonempty, not merely finite.
3. Coverage gives a stage containing every vertex; monotonicity
   moves that witness to a successor stage suitable for Nat.find.
4. The least-index proof excludes appearance in the preceding
   stage, including the n=0 corner case.
5. Uniqueness distinguishes the first-appearance index from
   an arbitrary later stage containing x. Only the first
   index defines its component.
6. Pairwise disjointness is derived from uniqueness; the
   argument does not presume a global linear order of vertices
   within each component.
7. Nothing here certifies back-edge reachability or the unary
   functional Fraisse-limit embedding property.

Seven separated mathematical challenge passes by this
assistant; no independent external referee agents were spawned.


## Adversarial audit: C0 descending dependency closure (13 October 2026)

1. **Dependency direction.** A back edge is an *unordered graph edge*
   with one endpoint in a new B_n and the other in the earlier A_n;
   it is not an arbitrarily oriented edge. Every target component
   has index <n; this prevents cycles between distinct components.
2. **Full component output.** The unary closure contains each whole
   reached block, not just a chosen old neighbour. Omitting the
   other vertices of a reached block would invalidate the
   manuscript's component equivalence.
3. **Finite character.** Reachability uses arbitrary finite directed
   paths, but its indices are all <=n. Thus a reachable component
   set is finite. Filtering `range(n+1)` adds no reachable vertex
   and discards none; no external well-founded recursion is assumed.
4. **Mutual reachability.** For vertices v,w in different components,
   mutual membership C(v),C(w) would imply each index <= the other,
   hence equality. Back-edge cycles cannot silently merge blocks.
5. **Closure nesting.** A proof of w in C(v) alone is insufficient
   to conclude C(w) subset C(v) without composing the reachability
   witnesses. `GenericC0Ancestor.trans` supplies that composition.
6. **Actual old neighbours.** The step that absorbs an old neighbour
   checks both `y∈A_n` and graph adjacency; mere adjacency to v
   could describe an internal/newer vertex and is not a back edge.
7. **Strongness and functional age.** The finite no-cross strongness
   lemma of PR #83 is a separate input; this module alone does not
   prove every finite unary-closed set strong, the functional
   Fraisse limit, or any Ramsey expansion.
8. **Independent regression.** The Python checker exhaustively
   constructs finite strictly descending component-dependency
   diagrams, with multiple block vertex multiplicities. This
   cannot replace the kernel-checked Lean proofs.

These are separate adversarial checking perspectives conducted
within one assistant session, not separately spawned human
or agent referees. PR #86 integrated CI run 38380094815 passed the 334-declaration standard-axiom audit and 74-file placeholder scan.


## Adversarial audit: C0 generated unary closure algebra

1. **Undefined/empty values:** the named unary closure has a
   finite *defined* value on every vertex; it is never confused
   with an undefined partial function value or an empty value.
2. **Closure contains generators:** `v∈C(v)` is proved from
   ancestry reflexivity; no unproved extensive-closure axiom
   is added to the Lean definitions.
3. **Idempotence:** follows from the nesting property
   `w∈C(v) ⇒ C(w)⊆C(v)`; the proof checks both inclusions
   and does not postulate that an iterated function stabilizes.
4. **Finite unions:** ordinary unary functions preserve
   finite unions of closed domains. This is intentionally
   *not* asserted for the unbounded set-input operations
   of the C_F presentation.
5. **Strong vs function-closed:** unary-closedness is a new
   predicate of finite vertex subsets. It is not silently
   equated with the intrinsic graph strongness predicate.
6. **Embedding scope:** these closure identities alone do
   not show the unary functional embeddings are the intended
   graph embeddings with back-edge-closed images, nor the
   free-amalgamation Fraisse property.

These six are adversarial mathematical checking perspectives
performed by this assistant, not externally spawned referees.
PR #87 original integrated CI run 38380760041 passed the standard-axiom and placeholder audits. Reconciliation with parent PR #86 is checked separately.


## Adversarial review: old-neighbour no-cross criterion

1. A graph edge is an *unordered two-element* set. The proof
   verifies any two distinct endpoints are adjacent using
   the graph's irreflexive symmetric adjacency predicate.
2. If an edge is neither contained in old a nor contained
   in selected x∪B, it has a vertex outside a and a vertex
   outside x∪B. The former belongs to B (using x⊆a),
   and the latter lies in a.
3. The two selected vertices are distinct because one
   is outside a and the other lies in a. This is needed
   before applying the two-element edge lemma.
4. The resulting adjacency is a genuine old back edge.
   The back-neighbour hypothesis puts its old endpoint
   inside x, a contradiction.
5. The no-cross statement itself does not require B∩a=∅
   or any strongness. The downstream closed-block lemma
   **does** require disjointness to identify the overlap
   as exactly x, and requires x≤a to preserve strength.
6. A regression over all labelled simple graphs on up to
   five vertices and all three-way vertex splits tests
   the cut criterion. It is diagnostic only; the Lean
   kernel proof and axiom scan are authoritative.
7. The full unary-closed-set strongness induction remains
   a separate theorem; no final manuscript marker is
   upgraded on this isolated finite criterion.

Seven mathematical adversarial proof checks by this assistant,
not independently spawned external referee agents.


## Adversarial verification: unary-closed sets are strong

1. **Whole-component dichotomy.** If a unary-closed set s
   meets B_n, the entire B_n lies in s. Without this step
   an intermediate extension need not contain all of B_n.
2. **Back-edge orientation.** Any old neighbour of a
   vertex of B_n is in C(v), hence in s. Internal block
   edges and edges toward later blocks are irrelevant.
3. **No-cross premise.** The finite graph cut
   `NoCrossEdges A_n ((s∩A_n)∪B_n)` is proved, not
   inferred from disjointness alone. The omitted old
   vertices have no edge to the added block.
4. **Inductive strengths.** The omitted-component case
   uses transitivity of `IsStrong`. The included case
   uses `closedBlock_strong_of_noCross` with the exact
   old intersection and disjoint B_n.
5. **Intermediate sets.** The local union lemma checks
   *all* intermediate sets in A_n∪B_n; it does not
   only compare predimension at the endpoint.
6. **Finite-to-infinite.** The target strongness is
   globally quantified over finite extensions in M0.
   An exhaustive finite strong stage containing the
   test extension allows the restricted strongness
   theorem to prove that exact global assertion.
7. **No false converse.** Globally strong finite graph
   subsets need not automatically be closed under the
   chosen enumeration's unary closure operation.
   No biconditional is claimed.
8. **Remaining functional theorem.** This does not by
   itself construct the Fraisse extension schedule of
   the unary age or prove equivalence of all embeddings,
   recurrence, big Ramsey degrees or Ellentuck axioms.

These are eight distinct hostile proof checks by the same
assistant, not separately spawned independent reviewers.
Original PR #89 integrated CI run 38382951195 passed the 356-declaration standard-axiom audit and 77-file placeholder check. Reconciled build will be checked separately.


## Adversarial audit: functional C0 embedding consequences

1. **Graph-embedded meaning:** the definition explicitly
   requires injectivity, preservation and reflection of graph
   adjacency, and equality of entire set-valued unary function
   outputs. Preservation of function membership alone is weaker.
2. **Reflection of closure:** from f(w) in C(f(v)), the
   equality f[C(v)]=C(f(v)) yields a preimage in C(v);
   injectivity identifies the preimage with w. No inverse
   image is assumed globally surjective.
3. **Component onto, not into:** mapping both mutual closure
   relations proves the forward inclusion; the reverse uses
   that every point of C(f(v)) has a preimage and mutual
   closure reflection. An injective map into a proper subset
   of a target component would not be a unary embedding.
4. **Finite closure commuting:** both directions of
   f[\langle S\rangle]=\langle f[S]\rangle use full
   set-valued equality, rather than an inclusion assumed
   to be sufficient.
5. **Finite strong images:** global strongness of f[S]
   is derived from f[S] being unary-closed and the
   separately certified `genericC0UnaryClosed_global`;
   it is not asserted for images of arbitrary finite
   globally strong subsets of the unexpanded graph.
6. **No mistaken converse:** an induced graph embedding
   carrying complete components onto complete components
   need not preserve the chronological direction of an
   edge between different components. Back-edge
   compatibility remains necessary to recover C(v).
7. **Scope:** this proof does not construct the full
   functional Fraisse limit, order it canonically or
   establish a Ramsey or Ellentuck theorem.

These are deliberately separate hostile mathematical checking
passes by one assistant, not independent external referees.
Integrated Lean CI, standard-axiom and placeholder checks pending.


## Adversarial checks: C0 directed back edges and embeddings

1. Back edges are defined using the *enumeration* component
   index; the underlying graph remains undirected. Adjacency
   alone does not distinguish a back edge.
2. Closure membership alone allows vertices inside the same
   component. The strict index difference is necessary to
   characterize an old neighbour.
3. For an adjacent vertex w in C(v) in another component,
   ancestry gives index(w) <= index(v); the inequality is
   strictly < because the component indices differ.
4. A unary embedding reflects closure membership using
   injectivity and equality of the entire finite function
   value, rather than assuming global surjectivity.
5. The old-neighbour-set image statement includes the
   difficult reverse inclusion: each old neighbour of
   f(v) lies in f[C(v)], hence has a preimage.
6. That preimage is proved to be an old neighbour by
   reflecting adjacency, closure and component difference,
   rather than presuming the image is closed under every
   graph neighbour.
7. This does not imply the full converse embedding
   characterization; a component-preserving induced map
   can reverse the chronological orientation of an edge
   unless directed back edges are also respected.
8. No functional Fraisse property, recurrent ordering or
   Ramsey/Ellentuck theorem is imported from this lemma.

Eight hostile checks performed within this assistant
session; no independent external referee agents.
Full Lean build, axiom and placeholder audits pending.


## Adversarial verification: full C0 embedding equivalence

1. **Correct embedding language:** the graph is still
   undirected, but the decomposition records directed
   back-edge incidences relative to the chosen minimal
   enumeration. There is no need for the map to preserve
   chronological order on incomparable components.
2. **Complete components:** the requirement is equality
   of f[B(v)] and B(f(v)), not mere inclusion. Surjectivity
   onto each target component is essential to lift all
   vertices reached by a target dependency.
3. **Complete back-edge sets:** the requirement is equality
   of images of old-neighbour sets at *each vertex*. An
   inclusion cannot exclude an extra target back neighbour
   outside the image.
4. **Forward path induction:** a source step from component
   j to an earlier component k is witnessed by a *real*
   vertex-level edge. Its target image is an old back
   neighbour, so all vertices of the reached component
   fall inside the target unary closure by nested closure.
5. **Reverse path induction:** a target step has a
   vertex-level witness; using the earlier reverse
   induction, lift its upper endpoint to a source vertex.
   Old-neighbour-set onto-ness lifts its lower endpoint.
   Component onto-ness then lifts every vertex of the
   reached target block.
6. **No phantom vertices:** each element of the target
   unary closure is reached in the reverse induction and
   acquires an explicit source preimage. No global
   surjectivity of the embedding is assumed.
7. **Boundary:** the root component is mapped completely
   and its source/target closure paths are reflexive.
   There is no omitted zero-length ancestor path.
8. **No overclaim:** the theorem is an equivalence of
   embedding *descriptions* for the fixed concrete
   presentation; it is not a Fraisse genericity proof
   for the unary functional age.
9. **Regression:** finite decreasing directed dependency
   diagrams are checked under all allowed permutations
   preserving the direction of present dependencies.
   This tests the important case where incomparable
   component indices may reorder.

These are separate adversarial checking passes by the
same assistant, not independently spawned referees.
CI and exact axiom audits are pending.


## Adversarial audit: C0 local minimality transfer (13 October 2026)

**Referee 1 — modularity:** The cancellation of relative
predimensions holds for **all** P⊆D⊆P∪B. Checking only
D=P∪B would not suffice to transfer strongness, which
quantifies over all intermediate sets.

**Referee 2 — overlap:** The equality A∩D=P uses both
P⊆A and A∩B=∅. If the new block contains an old
vertex, local and enlarged relative predimensions can differ.

**Referee 3 — no crossing:** NoCrossEdges A (P∪B) is
essential. A new B-vertex adjacent to an omitted old
vertex of A\P invalidates the cancellation identity.

**Referee 4 — local self-sufficiency:** Strongness of
A in A∪B gives a predimension lower bound for every
A∪D. Relative cancellation transfers it to P⊆D⊆P∪B,
not just the entire B.

**Referee 5 — lifting intermediates:** A local strong
intermediate D lifts to A∪D strongly inside A∪B.
The proof explicitly intersects each competing enlarged
intermediate with P∪B and uses cancellation on both D
and the intersection.

**Referee 6 — minimality:** Minimality of A⊂A∪B rules
out any proper strong A∪D. Disjointness of B from A
is used again to turn the two possible enlarged
endpoints back into D=P or D=P∪B.

**Referee 7 — scope:** This proves *descent* of minimality
to the local lower closure. Its converse (free-amalgamation
stability) is not yet Lean-certified, nor is the actual
lower-closure P of an enumerated C0 component.

**Referee 8 — independent diagnostic:** A regression checks
all labelled simple graphs on at most five vertices and
three-way partitions into P, A\P, B satisfying no crossing.
It tests strongness and minimality of both extensions,
independently of the Lean proof. This finite computation
is a diagnostic only.

These are separate adversarial mathematical checking passes
of one assistant, not independently spawned external agents.


## Adversarial review: two-way C0 minimality under free amalgamation

1. Every enlarged intermediate has the form
   Z=A∪(Z∩(P∪B)); skipping one invalidates minimality.
2. The no-cross predimension identity applies to all
   intermediates, not only the endpoints.
3. A locally strong intermediate D lifts to A∪D strongly;
   conversely an enlarged strong Z restricts to a locally
   strong D=Z∩(P∪B).
4. The two endpoint cases D=P or D=P∪B recover exactly
   Z=A or Z=A∪B; neither can have additional tail vertices.
5. A∩B=∅ is needed for strictness and to identify the
   actual common base as P.
6. No global strongness of P inside A is presumed, nor
   a special generator or order on B.
7. The independently implemented five-vertex regression
   in PR #93 checks minimality equivalence exhaustively
   for all no-cross three-way partitions.
8. Free-amalgamation persistence of one finite increment
   is not a proof of functional Fraisse genericity.

These are hostile mathematical checking perspectives of
the same assistant, not independent external referee agents.


## Adversarial checks: the concrete local C0 lower closure

1. The local lower part is the **whole** unary closure C(v)
   minus its original component B(v), not merely its immediate
   old graph neighbours. Omitting predecessor components
   would invalidate the local strongness claim.
2. Every predecessor component in C(v) has strictly smaller
   index than B(v); hence P(v) lies inside the old prefix.
3. Unary closedness of P(v) follows from ancestor transitivity
   and decreasing indices. Removing B(v) cannot leave a
   dependency pointing *back upward* into B(v).
4. P(v) and P(v)∪B(v) are globally strong by the full
   unary-closed-set theorem, not by assuming a strong
   substructure of M0 is automatically unary-closed.
5. The no-cross hypothesis is proved from unary-closedness
   of C(v) and inclusion of the *whole* new block.
   It is not inferred merely from absence of arbitrary
   edges to later blocks.
6. The original global minimal-step theorem applies to
   the actual finite enumeration stage, and the exact
   stage union A_i∪B_i=A_(i+1) is used to rewrite its target.
7. For each x∈B(v), the intrinsic strong closure
   `cl_s(P(v)∪{x})` is the whole local component extension.
   No assumption that x is the designated generator enters.
8. The extension over a freely amalgamated larger old
   graph is a different assertion requiring reverse
   local-to-enlarged strongness/minimality; not claimed here.

Eight separately framed adversarial checks by this assistant,
not independent spawned agents. Integrated Lean audit pending.

**Ninth referee check — free persistence:** the concrete API explicitly requires the larger old set to contain the entire lower closure, be disjoint from the new block and have no crossing edges. It applies the independently audited reverse minimality-transfer theorem; it makes no assertion for arbitrary graph extensions with extra old-new edges.


## 13 October 2026 — prepared-block concatenation audit

Three independent mathematical attack surfaces were reviewed before
introducing `C0PreparedBlocks.lean`:

1. **Missing hypothesis counterexample.** Local minimal strongness
   is not sufficient to attach a block to an arbitrary old graph.
   With P empty, B a singleton and A three isolated vertices all
   adjacent to the new vertex, the local step is minimal strong but
   the enlarged step is not strong. The no-cross certificate for
   every current prefix is indispensable.
2. **Boundary audit.** The proof must preserve minimality at each
   successive attachment, not merely strongness of the final union.
   A strict local minimal step and disjoint fresh block prevent
   empty increments. Induction uses the *updated* prefix A∪B.
3. **Overclaim audit.** This establishes a finite graph chain, not
   the functional closure values of a tagged amalgam. A separate
   reachability/closed-base argument is required to identify the
   interleaved functions with those inherited from both factors;
   fairness in M₀ is a further independent countable step.

The kernel proof `GraphOn.preparedBlocks_minimalStrongChain` passed
full CI run 38481016951 (390 standard-axiom declarations and 84
placeholder-free Lean files). Its finite graph scope is unchanged.


## 13 October 2026 — heredity of the C0 minimal-component presentation

**Referee A (minimality):** A closed set meeting B_n must contain the
whole block; otherwise the cut can have genuine intermediate strong
substructures. In the triangle component example, taking the old A and
only two of its three new vertices leaves A⊊A∪{x}⊊A∪{x,y}
with A∪{x} strong in A∪{x,y}. The original full block B is minimal,
but this cut is not.

**Referee B (predimension):** The restricted minimality proof needs
the stronger no-cross condition with the full original old prefix,
not merely a common numerical predimension. This is exactly the
certified `genericC0UnaryClosed_noCross` lemma.

**Referee C (induction):** Skipped enumeration components must be
treated as equal successive cuts; an inductive minimal chain
must append only strict included-block steps. The proof introduces
`MinimalStrongChain.append` rather than inserting empty steps.

**Referee D (scope):** Finite minimal presentations of induced
closed subgraphs do not ensure that an arbitrary tagged functional
amalgam retains inherited unary values, and do not schedule the
extension property in the ambient countable graph.

All four are independent adversarial proof perspectives applied to
the definitions and argument, not independent external referee agents.
The exact hereditary endpoints passed full CI run 38481909334
(397 standard-axiom declarations, 85 placeholder-free files).


## 14 October 2026 — tagged functional free-amalgamation audit

Four separately developed hostile arguments challenge the proposed
bridge between graph free amalgamation and unary closure values.

1. **Base agreement adversary.** If the two dependencies differ on
   the common base, a path can be added without leaving the base.
   Two base components p,q and only the right edge p→q are a minimal
   counterexample to preservation.
2. **Base closedness adversary.** Even if base dependencies agree,
   a right back-edge p→r to a fresh right component changes the
   left closure of p. Thus each input factor must close the
   *complete* common base under dependency successors.
3. **Spurious cross-path adversary.** A free join of *graphs*
   excludes left-tail/right-tail edges, but equality of graph
   edges on factors alone does not exclude new directed closure
   paths via a non-closed common base. The tagged dependency
   relation is checked separately from graph adjacency.
4. **Transfer/typing adversary.** A path theorem for component
   indices need not automatically imply literal equality
   of vertex-valued unary functions until the component
   partition and component-to-vertex unfolding are fixed.
   The finite Finset-valued dependency closure theorem is
   therefore a bridge, not a complete proof of the actual
   C0 functional age or its countable Fraisse extension.

Exhaustive diagnostic test:
scripts/check_c0_tagged_dependency.py evaluates 10,276 tagged
diagrams, 60,552 closure equalities, and explicit failures when
agreement or closedness is removed. The exact Lean statements passed integrated CI run 38485892107:
405 declarations with standard logical axioms only, 86 Lean files
without placeholders, and all finite regressions.


## 14 October 2026 — complete C0 component values and old-prefix persistence

Referee 1 (off-by-one): The first-appearance index of v is the
unique i for which v∈B_i=A_(i+1)\A_i. Thus the correct bound for
v∈A_n is i<n. The closure inequality index(w)≤i then gives w∈A_n.

Referee 2 (named function vs graph): Global strongness of a prefix
does **not** imply that it is closed under the enumeration-dependent
unary function. The new theorem proves unary closedness from
descending component dependencies, not predimension.

Referee 3 (unfolding adversary): A closure equation on component
indices can hold while the vertex-valued function changes if the
target component contains a new vertex outside the source image.
The theorem therefore requires equality of complete block images.

Referee 4 (diagram generality): Component blocks need not be
pairwise disjoint for the abstract union-transport equality, although
actual closure-components are disjoint. Regression tests include
both disjoint and overlapping blocks.

Referee 5 (scope): These proofs certify finite closure-value
transport and the closedness of the **already constructed** C0
countable enumeration stages. They do not prove that a separately
fairly scheduled functional enumeration exists, nor certify that
every finite permitted functional diagram is realized.

These are separate mathematical adversarial checks by this
assistant, not independently recruited external human referees.

The whole-component unfolding and unary-prefix theorems were
subsequently certified by full Lean CI run 38486803292:
411 declarations with standard logical axioms only; 88 Lean
files checked for placeholders; 121,104 whole-block value comparisons.
The scope limitations stated by the five adversarial perspectives
remain in force despite these successful audits.


## 14 October 2026 — adversarial review of the one-block response theorem

**Graph referee.** Mere injective homomorphisms are insufficient:
nonedges matter when comparing strong intermediate subgraphs.
The new theorem requires an induced embedding and transfers
minimality in *both* directions by an exact filtered preimage.

**Predimension referee.** Under an induced isomorphism every
finite induced edge count and predimension value is unchanged.
An intermediate set in the image is not assumed to be a literal
substructure of the old carrier: its filtered preimage is proved
to have exactly that image before applying minimality.

**Fraisse referee.** Realising an unlabelled type is not the
extension property needed by the manuscript. The response uses
the labelled strong-diagram theorem and certifies g(inl x)=x.val
for every old vertex. It also verifies the finite response image
is *globally strong* in M0.

**Counterexample referee.** Dropping inducedness changes minimality:
the complete graph K4 has a minimal strong step from a singleton
old base to all four vertices, but the edgeless graph on the same
set does not. Dropping injectivity can collapse a singleton
extension entirely.

**Functional genericity referee.** Although the response theorem
produces a minimal new graph increment over a chosen strong
prefix, it does not endow the existing fixed enumeration with
new positions. The still-open countable fair scheduling theorem
must build its own chain, and preservation of named unary values
must be established at each step.

These are independently structured adversarial tests by this
assistant, not human or separately spawned external agents.


## 14 October 2026 — hostile review of tagged one-block amalgamation

Referee A (component overlap): the right fresh block is the
literal finite difference of right and left domains, while their
intersection is the entire common base. Both set identities are
proved explicitly and used to prevent duplicated base vertices.

Referee B (predimension): a local minimal strong extension can
be enlarged freely over an arbitrary old graph only under the
no-cross condition. The existing modular predimension lemma
guarantees all intermediate relative predimensions agree, not
merely their endpoints.

Referee C (sparsity): the common base must be strong in the
left factor to invoke the strong tagged amalgamation theorem;
right-base strength comes from local minimality. Omitting
this premise from the 2-sparsity statement would overclaim.

Referee D (embedding): actual induced adjacency and nonadjacency
on both input factors are inherited from the tagged free graph,
under explicit agreement on P.

Referee E (scope): the new result is a finite canonical
amalgamation theorem. Turning an arbitrary embedded closed
base in a literal old finite subset of M0 into the canonical
P⊕L presentation, then feeding this graph to the labelled
response, are remaining steps. It does not prove the countable
generic functional extension property.

These are adversarial mathematical checks, not independently
recruited external human referees.


**Sixth check (regression admissibility).** The first small-model
test wrongly required a minimal strong extension in every possible
combination of base size and new-block size. This is false; over an
empty base no two-vertex graph produces a minimal strong extension.
The checker now enumerates the admissible diagrams without demanding
existence in impossible parameter classes, and explicitly includes
the nontrivial K4 example with one old and three new vertices.
The first CI run compiled and audited 418 Lean declarations
(standard logical axioms, no proof placeholders), then failed at
this diagnostic assertion rather than at the mathematical theorem.
The corrected regression must pass before merging.


## 14 October 2026 — five adversarial checks for reduct identification

**Closed-set referee.** Local finiteness is essential: the
f_Cl-closure of a finite graph-strong A must be finite. The
proof obtains global graph strongness of each finite
f_Cl-closed C by testing inside a larger finite closed D,
not by incorrectly assuming a strong graph embedding is
automatically a functional embedding.

**Free-amalgam referee.** In C⊕_A B the base A need not be
unary-closed. The free amalgam is taken in the *graph*
language, where A is strong in both C and B. Only after
forming the two-sparse strong amalgam does one add the
functional components of D\C. An amalgam over a nonclosed
functional base would be invalid.

**Component referee.** The new minimal strong blocks are
inserted *after* all components of C. This preserves
complete old unary closures. The finite selected-block
strongness theorem checks both the whole-component
dichotomy and all back-neighbour dependencies; neither
hypothesis may be discarded.

**Genericity referee.** The functional Fraïssé limit
realises the newly expanded D over the entire closed C,
not merely over the original possibly nonclosed graph A.
Restriction to the original B is strong because B≤D
and D is graph-strong in the reduct.

**Enumeration referee.** An arbitrary minimal enumeration
of M0 need not yield the functional Fraïssé limit.
Only existence follows: a closed exhaustion of O
can be refined compatibly and transported through
the graph-reduct isomorphism. The revised manuscript
makes this existential qualification explicit.

The adversarial perspectives are distinct mathematical audits,
not independently recruited human referees. The exhaustive
finite regression is a separate executable counterexample
search. The full functional Fraïssé identification remains
unformalised even if these finite lemmas pass CI.

The exact finite closed-block strongness theorem passed GitHub Actions
run 38503592428: 421 declarations with standard logical axioms,
92 Lean files scanned for placeholders and full finite regressions.
The separate strong-span regression checked 1,846 amalgamation diagrams,
21,103 unary-closed selected subsets and preservation of 4,441 old
unary-function values. These finite certificates do not replace
the pending functional Fraïssé reduct-identification theorem.


## 14 October 2026 — independent adversarial passes: absolute strong factorisation

1. **Hypothesis minimisation.** A finite strong pair A≤D
   suffices; no strong exhaustion or global strongness of
   D is needed. The proof selects an intermediate strong
   C by minimum cardinality among finitely many candidates.
2. **Strongness direction.** From A≤D and A⊆C⊆D,
   strong restriction gives A≤C. If Z≤C and C≤D,
   strong transitivity gives Z≤D. Both directions are
   required; reversing either invalidates the argument.
3. **Strict progress.** C properly contains A. Selecting
   any v∈C\A witnesses strict decrease of the finite
   complement D\C, which supplies the induction measure.
4. **Counterexample to unnecessary globality.** In the
   four-vertex star with three leaves and one centre,
   the three-leaf induced subgraph is two-sparse and
   ∅ is strong inside it, but its predimension drops
   on adding the centre. Requiring the upper endpoint
   to be ambient-globally strong would exclude a
   legitimate finite minimal-step decomposition.
5. **Free-amalgam scope.** The resulting tagged free
   graph preserves induced factor embeddings, their
   exact common base, and strongness. None of these
   facts by themselves provide a functional Fraïssé
   extension or identify an enumeration with M0.

This is an internal adversarial audit with executable
finite-model checking, not a claim of external human
referee certification.


## 14 October 2026 — adversarial panel: finite unary closure certificates

1. **Complete-component referee.** A vertex inside an increment
   must bring the entire increment into its unary value. Closure
   under only the old neighbours does not preserve strongness;
   the K4 selection {a,x,y} is a concrete counterexample.
2. **Old-neighbour referee.** Whole component membership alone
   is not enough: in K4, the three new vertices form a complete
   minimal strong block over a, but omitting a produces a
   non-strong selected subgraph.
3. **No-cross referee.** The graph has no crossing edge between
   the selected new block and unselected old vertices because
   every such edge would end at a named unary predecessor.
   This is the exact hypothesis of the finite strongness lemma.
4. **Closure-language referee.** The function is set-valued;
   C-closed means C(v)⊆X for every v∈X. It must not be replaced
   by pointwise adjacency or by closure under only one vertex
   of a multi-vertex component.
5. **Formalisation-scope referee.** The new Lean theorem derives
   the finite selected-block certificates from explicit
   pointwise properties of C. Proving those properties for the
   canonical reachability-defined function in every abstract
   finite age presentation is the next bridge; it does not
   follow from the theorem's hypotheses automatically.

These are separately structured adversarial mathematical checks,
not claims that independent human or external agents reviewed the proof.


## 14 October 2026 — adversarial audit of canonical finite C0 values

**Referee A: indexing.** Each vertex belongs to exactly one
fibre of κ:V→Fin n; the old prefix contains precisely the
vertices with smaller index. The equalities A_0=∅,
A_n=V and A_(k+1)=A_k∪B_k are checked formally, including
n=0 when V is necessarily empty.

**Referee B: paths.** The named unary value is defined by
full *component reachability*. The root step forces every
vertex in B_(κ(u)) into C(u), irrespective of how many
vertices it has. One old-neighbour edge is a directed
dependency and therefore makes that neighbour belong
to C(u). No decomposability approximation is substituted.

**Referee C: closed selections.** If s is closed under C
and meets a new block, it contains the block and all its
old neighbours. Hence any edge from the new block into
the omitted old vertices is impossible. These are the
exact two certificates for the finite no-cross strongness
lemma, not an unsupported assertion that every union of
whole blocks is strong.

**Referee D: hypotheses.** Only finite strong steps
A_k≤A_(k+1) are needed. Requiring the final finite graph
to be globally strong in a larger ambient graph would
exclude valid finite age presentations, as shown by the
previous three-leaf-star counterexample.

**Referee E: exhaustive models.** The checker runs all
small simple graphs and all choices of chronological
component indices, including unused values of κ and
components with several vertices. It checks full unary
values and graph strongness of each unary-closed set.
The earlier K4 examples separately demonstrate failure
when either complete-block closure or old-neighbour
closure is removed.

**Referee F: claimed scope.** This is the exact finite
canonical closure calculation needed by the manuscript's
hereditary strongness proof; it does not prove that a
functional reduct of an infinite Fraïssé limit satisfies
all required extension properties. Those steps remain
PARTIAL until linked to the explicit finite-age
amalgamation and strong-reduct lifting theorem.

These are independent adversarial mathematical passes
conducted within this validation, not claims of
separately recruited external human referees.


## 14 October 2026 — adversarial audit of finite canonical heredity

Six independently structured attack surfaces were examined.

1. **Chronological cuts.** A selected set X meets a component
   B_k either not at all or completely. The proof explicitly
   distinguishes equality of X_(k+1)=X_k from a proper
   minimal strong extension.

2. **Old-neighbour closure.** The hypothesis that X is closed
   under the *entire* reachability-defined unary value forces
   every old neighbour of a selected new block to lie in X_k.
   This is the no-cross certificate with the correct old
   stage A_k, not just an assertion about some closed base.

3. **Relative predimension.** Minimality of A_k<A_(k+1)
   descends to X_k<X_(k+1) under no-crossing. It would be
   incorrect to infer minimality from the already certified
   strongness of X_k in A_k alone.

4. **No global exhaustions.** Every step is a finite
   strong extension, and the endpoint is finite. The proof
   uses no globally strong ambient structure.

5. **Omitted and empty blocks.** Empty indexing positions
   and omitted components must be erased rather than
   made into fictitious minimal strong steps. The proof
   concatenates only strict steps, with equality cases
   passed through unchanged.

6. **Exact scope.** The result provides a minimal graph
   presentation on the vertices of an f_Cl-closed subset.
   A separate lemma should show that the unary function
   *inherited* from the original finite structure coincides
   with the canonical backward-reachability function after
   the retained components are reindexed.

This is an internally conducted adversarial mathematical
audit supported by finite exhaustive models, not a claim
of external human referee certification.


## 14 October 2026 — adversarial panel: full finite functional heredity

Seven distinct mathematical failure modes were examined.

1. **Lost intermediate path witnesses.** A path may have several
   backward dependency edges. Restricting its endpoints to a
   vertex set would not preserve it if intermediate witnesses
   were deleted. The proof uses *full* closure of s under
   f_Cl(u) to put every witness of every reached component
   into s before lifting the path.

2. **Incorrect graph restriction.** The restricted graph is
   the induced pullback along the subtype inclusion W→V.
   This preserves and reflects adjacency on selected
   vertices. The theorem does not apply to a mere
   graph homomorphism or weak noninduced copy.

3. **Incomplete components.** The function values contain
   all vertices of every reachable component. If s cuts
   a component, restricting the function by intersection
   can yield a different structure. The prerequisite
   IsClosedUnderValues prevents this.

4. **Base old neighbours.** An edge from a selected
   new block to an omitted old vertex would disappear
   on restriction. Complete backward reachability
   explicitly forbids that edge when the set is closed.

5. **Unnecessary chronology compression.** The finite
   age definition already allows empty increments.
   Retaining the old κ-indices in the subtype avoids
   any need to choose a new linear order of the
   selected components; the path relation remains
   literally comparable index by index.

6. **Strong versus minimal steps.** The induced graph
   inherits strict minimal strong steps only after
   applying the already certified local no-cross
   transfer and induced-image minimality theorem.
   Function-value preservation is separately proved
   and cannot replace this step.

7. **No countable overclaim.** The results close finite
   functional heredity for canonical presentations.
   They do not on their own construct the class's
   free functional amalgam or establish strong graph
   extension for the reduct of its Fraïssé limit.

These are separate adversarial mathematical arguments
performed within the review, not external human referees.


## 14 October 2026 — adversarial panel: no changes to old unary values

**Referee A (dependency direction).** Every direct dependency
strictly decreases the component index. The proof inducts
over whole dependency paths and excludes any increase of
the starting index, hence any path from an old block to
a future block. Reversing this orientation is a concrete
failure mode.

**Referee B (graph edges across the boundary).** A newly
appended block may have graph edges to the old prefix.
Those edges contribute dependencies starting in the *new*
block and pointing backward; they do not create new
backward paths from old vertices. The theorem does not
forbid these edges.

**Referee C (induced old part).** The old prefix is taken
as an induced subgraph. Introducing an edge between two
old vertices could create a new old-to-old dependency
and enlarge unary values; such an operation is not
covered by the theorem.

**Referee D (complete closure).** The value consists of
full vertex components reached along arbitrary-length
dependency paths. The test compares entire bitsets of
vertices, rather than only immediate neighbours.

**Referee E (unnecessary hypotheses).** The persistence
statement needs no sparsity, strongness, or minimality
assumption. These hypotheses are needed elsewhere to
form an admissible finite C0 extension, not to show
the function of old vertices stays fixed after one
has been formed.

**Referee F (countable interface).** These finite
results justify a key invariant when new minimal
blocks are appended, but do not replace construction
of the finite functional extension diagrams or the
countable Fraïssé extension-property proof.

The six perspectives were independently structured
adversarial checks within this review; no external
human referees were recruited.
