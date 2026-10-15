# Adversarial audit: strict d-closedness through a finite run
15 October 2026

Let A be the old finite stage and B1,...,Bk disjoint successive
fresh blocks. The new reusable Lean predicate
GraphOn.IsLocalDClosedBatchRun requires at step i:

* a strictly d-closed support P_i in the **current prefix** A_i;
* no old neighbour of B_i outside P_i;
* a fresh disjoint block B_i;
* a minimal strict d-closed extension P_i <_d P_i∪B_i;
* exact recovery cl^d_(P_i)(N_(P_i)(B_i))=P_i.

The certified one-block support-persistence lemma then gives
A_i <_d A_i∪B_i. The new general theorem composes the steps
into a finite MinimalDClosedChain and proves A≤d A_k
by transitivity. In particular it covers intermediate sets
meeting vertices from several consecutive blocks.

## Four adversarial referees

**1. Initial versus current base.** Knowing P_i≤d the
*original* old stage is not identical to the hypothesis
P_i≤d the current prefix. A future instantiation for the
concrete tagged stage must transport d-closedness from the
original old stage along the already certified preceding
steps. The new run predicate deliberately requires the
current-prefix condition rather than concealing this
induction.

**2. Proper increments.** Minimal d-closed steps exclude
empty increments. A chain that silently permits B_i=∅
would not be a chain of minimal increments. Our one-block
minimality condition enforces nontriviality at every step.

**3. Strictness across two blocks.** The endpoint assertion
A≤d A_k is not a consequence merely of having no crossing
edges. It follows because every genuine one-block step is
strictly d-closed and that relation is transitive.
The independent diagnostic checks every intermediate set
in small two-block examples, including multivertex blocks
and nonempty old supports.

**4. Class/graph separation.** This is an abstract finite
run with explicit successive hypotheses. It does not
yet show that the *specific tagged simultaneous graph*
satisfies those hypotheses for a chosen enumeration of
its complete request set. Neither does it prove that
the resulting graph belongs to the concrete class C_F
or construct the countable limit. Those require the
tagged graph's full local-induced theorem, absence of
cross-block edges, and the standing class-level
free-amalgamation assumption.

CI must pass on the exact Lean theorem endpoints and
the independent two-block regression before a green
manuscript marker is added. This note does not assert
that the entire concrete C_F level schedule has been
formalized.
