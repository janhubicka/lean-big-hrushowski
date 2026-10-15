# Adversarial audit — fair d-closed extension requests in a countable C_F graph

15 October 2026

## Exact conditional theorem

Fix a growth bound F on natural-number cardinalities and a graph G
on a countable carrier ℕ. A finite request is a labelled complete
growth-class diagram A≤d B, with an induced d-closed embedding of
A into B and a proposed injective induced map of A into G.

The theorem assumes a covering chain of finite strictly d-closed
stages and the following explicit schedule condition:

> Whenever the fair enumeration names a request applicable to the
> current finite stage, the next finite stage contains a d-closed
> induced copy of its target extending the prescribed source map.

Under that condition every finite globally d-closed extension
request has a globally d-closed response in G.

This result does not assert that a particular level construction
already supplies the required chain or all scheduled responses.

## Four mathematical adversarial referees

**1. Countability and complete diagram referee.**
At fixed finite source and target sizes there are finitely many
complete graph codes and embedding maps. The d-closed, induced,
growth-membership and injectivity fields are propositions, not
additional coding choices. Hence the sigma family of all labelled
diagrams and finite maps into ℕ is countable. Merely cataloguing
unlabelled isomorphism types would not suffice, because a request
specifies the *actual* embedding of its source into the ambient G.

**2. Fair recurrence referee.**
Decoding a request once is not enough: it might be examined before
its finite source embedding appears in a stage. The Nat pairing
scheme revisits each encoded request at unboundedly many indices;
for every threshold n there is a later stage k≥n naming that
request. The script independently checks a finite pairing model,
while Lean proves the exact Nat.pair/unpair statement.

**3. Strict finite-to-global referee.**
A globally d-closed source image, once contained in stage U_k,
is d-closed in U_k by restriction. The stage response target is
d-closed in U_{k+1}; since U_{k+1} is globally d-closed by the
separate covering-chain theorem, strict transitivity gives a
globally d-closed target image. This step cannot be made with
weak strongness in place of strict d-closedness.

**4. Growth and actual-construction referee.**
The countable criterion quantifies over finite diagrams whose
source and target belong to the actual growth-function class.
It does not follow from mere 2-sparsity or from an arbitrary
monotone growth function. The finite stage membership theorem
from PR #148 is conditional on the stated C_F free-amalgamation
hypothesis. Even after that theorem and this abstract criterion,
one must construct the *coherent countable stage graph* from
varying dependent finite tagged carriers, arrange its stage
orders, and show that every applicable schedule request is
answered. Only then can one identify the reduct with M_F.
The functional block-root recovery and embedding monoid are
separate further goals.

## Independent finite diagnostics

scripts/check_cf_dclosed_fair_criterion.py checks recurrence
of repeated pairing indices and strict promotion of d-closed
finite responses to globally closed finite ambient graphs
over all small labelled graph codes. The supporting chain
checker includes the K4 strictness and K5 missing-coverage
counterexamples. These bounded computations complement the
general Lean theorem.

A green marker is permitted only for the exact conditional
countable criterion after the final integrated Lean build,
standard-axiom audit and placeholder scan. It must not be
used to mark the actual C_F countable construction completed.
