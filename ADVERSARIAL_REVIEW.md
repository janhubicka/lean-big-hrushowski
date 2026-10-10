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


## Finite strong-diagram completeness — adversarial review

**Labelling:** The chosen Fin(card A) and Fin(card B) presentations are equivalences, so the vertex counts and all induced adjacency and nonadjacency statements are preserved. No canonical labelling is claimed.

**Strongness:** The target-side predicate is checked on every intermediate finite substructure. Under the target equivalence, the labelled image of the base is exactly the original image of the source map. Thus the strongness predicate is not inferred merely from nonnegative full-graph predimension.

**Source and target sparsity:** Each is transferred through the separately audited 2-sparsity invariant for induced embeddings; every induced subset is covered.

**Enumeration boundary:** The theorem asserts existence of a labelled representative for a given finite strong embedding. It neither chooses labels uniformly in the source graph nor constructs a countable chain answering requests.

**CI boundary:** The theorem and all dependencies compiled in [run 38061458133](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38061458133); the axiom audit reported only standard logical axioms and no placeholders. These are separate hostile review perspectives applied by one assistant, not external independent human referees.
