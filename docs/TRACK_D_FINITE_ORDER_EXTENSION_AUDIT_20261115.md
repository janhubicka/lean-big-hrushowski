# Track D: finite order extension over a closed lower part (15 November 2026)

Status: **English lemma and adversarial audit only**. This note adds no Lean theorem or manuscript validation marker. It is stacked on candidate raw finite-age converse PR #587 and depends on its Lean certification.

## Exact finite extension lemma

Let (S,E,C) be a finite functional C₀ structure, with C reflexive and nested, and let E be symmetric and irreflexive. Assume the edge-cover property:
for any edge xy, either y belongs to C(x) or x belongs to C(y).

Let Q be a finite C-closed subset of S with an existing linear order <_Q. Let B be a nonempty set disjoint from Q, and put D=Q∪B. Assume:
(i) D is C-closed;
(ii) for each b in B, C(b)=D;
(iii) the already prescribed orders on C(q), q in Q, are coherent with <_Q;
(iv) the local ordered-isomorphism type of (D,E,C) over the ordered lower part Q is selected as the lexicographic minimum of the COMPLETE incidence and unary matrices obtained by permuting B, leaving the increasing enumeration of Q fixed.

Then there exists an extension <_D of <_Q with Q before B, such that:
* for each q in Q, the induced order on C(q) is unchanged;
* for each b in B, the induced ordered structure on C(b)=D realizes the selected ordered-isomorphism type;
* this statement is invariant under isomorphisms carrying the **ordered** Q to another ordered lower part.

**Proof.** Because B is finite, the set of permutations of B is nonempty; the finite set of complete two-matrix codes has a least element. Choose an enumeration attaining this minimum and put all of Q, in its prescribed order, before B in that enumeration. Closure of Q gives C(q)⊆Q for each q∈Q, so its induced order is unchanged. Every b∈B generates D, so the selected ordered type is realized on all of C(b), with no distinguished generator. An isomorphism preserving the ordered lower part transports the enumerations of B bijectively, preserves the complete codes, and hence preserves their minimum. QED.

**Useful graph consequence.** Suppose Q is C-closed in a larger structure S, D=Q∪B is C-closed and each b∈B has C(b)=D. Then there is no edge between B and S\D. Indeed for b∈B and x∈S\D, the edge-cover property would imply x∈C(b)=D or b∈C(x). The first is impossible and the second contradicts C-closedness of S\B only if S\B is C-closed. Thus the correct hypothesis for the no-cross-edge conclusion is that the old part A=S\B is C-closed (and includes Q). Under that additional hypothesis, b∈C(x) is impossible for x∈A. In a one-stage extension S=A∪B, C(b)=Q∪B with Q⊆A, every edge from B to A therefore ends in Q.

This refinement matters: **C-closedness of Q and D alone does not rule out edges from B to points outside D whose C-values contain B**. Do not weaken the hypothesis in a Lean lemma.

## Composition along a finite canonical stage presentation

Suppose S has a finite sequence of component stages S₀⊂...⊂Sₙ=S, where every Sᵢ is C-closed, Bᵢ=Sᵢ₊₁\Sᵢ is a nonempty minimal strong component, and every b∈Bᵢ has C(b)=Pᵢ∪Bᵢ for a C-closed Pᵢ⊆Sᵢ. Starting with the empty order, apply the preceding extension lemma to the closed local diagram Dᵢ=Pᵢ∪Bᵢ, using the induced existing order on Pᵢ, and append Bᵢ to the existing order on Sᵢ in its selected top enumeration. Then the resulting order is coherent on every one-generated closure C(x) already encountered. Empty stage indices can be ignored without altering the order.

This produces an order **for one given finite presentation**, provided the local type selection is indexed by the ordered lower-part data. It does not identify the choices made for different presentations of the same raw finite carrier, and it does not produce a pointwise isomorphism-invariant labelled order on all raw occurrences.

## Adversarial checks

1. **Full language:** the minimizing code must contain the entire graph matrix (including nonedges) and all unary C-memberships, not merely the edges adjacent to a generator.
2. **No physical canonical order:** if the minimizer is attained more than once, the result is one ordered isomorphism type; a named vertex order is a chosen representative of that type. For example, the K₄ stage over a singleton has an S₃ symmetry and cannot admit a labelled order fixed by all automorphisms.
3. **Old lower part fixed:** only permutations of B are allowed. Reordering Q would violate previously established closure orders.
4. **One-generated closures:** Q is C-closed, so old closures do not change; all b∈B have the whole D as their C-value. The argument never singles out one b.
5. **Strongness is not used in the order-selection proof:** it is needed earlier to justify that the finite component sequence represents the correct finite C₀ age. This separation can shorten the manuscript.
6. **No-cross-edge claim:** it requires the entire old part A to be C-closed, not just Q. The conditional proof above explicitly avoids the stronger false assertion.
7. **Global gap:** finite local order extension does not establish a coherent choice over all overlapping raw occurrences or embeddings. For W, construct a fair chronology, attach ordered-type keys to new components, show extension and restriction compatibility, and then establish the return map ψ. The five-vertex tie-break counterexample in docs/TRACK_D_UNIFORM_LOCAL_ORDER_SELECTION_20261108.md remains an obstruction to raw-name tie-breaking.

## Suggested Lean decomposition

* Prove the one-stage order extension for a finite local diagram using the existing `C0CoordinateTopPermutationOrbit` and `C0CoordinateFixedMatrixOrder` modules.
* Prove preservation of the order on each C(q) for q in the closed lower part.
* Induct on a *given stage presentation* to produce an ordered finite expansion, rather than claiming that arbitrary raw-host orders agree.
* Prove a separate transport theorem over ordered lower-part isomorphisms; Track A PR #588 supplies an automorphism-orbit interface.
* Only after these proofs and exact-head standard-axiom/placeholder audits may the manuscript claim a validated ordered finite-age statement.

This note deliberately does **not** assert that the existing selected catalogue is complete or hereditary without a construction.
