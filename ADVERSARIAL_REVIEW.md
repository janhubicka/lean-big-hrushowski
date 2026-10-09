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
