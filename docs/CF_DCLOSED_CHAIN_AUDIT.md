# Adversarial audit — global strict d-closedness from a finite-stage chain

15 October 2026

## Statements

Predimension.DClosedChain is a countable sequence of finite vertex
sets (U_n), together with genuine **strict** d-closed inclusions
U_n≤d U_{n+1} and a covering condition saying that every ambient
vertex belongs to some stage.

It does not assume a growth function or a specific graph class.
The main conclusion is that, for every n, U_n is **globally
d-closed**: δ(U_n)<δ(X) for every finite proper extension
U_n⊊X in the entire ambient carrier.

## Four mathematical adversarial perspectives

**1. Globality and coverage.**
Choose any finite X⊇U_n in the ambient structure. Coverage
implies X∪U_n lies in some stage U_m; monotonicity then puts
it in U_max(n,m). The finite transitivity of strict closure
gives U_n≤d U_max(n,m), which supplies the desired strict
inequality for X. Without coverage this is false: in K5 the
constant empty sequence has every successor inclusion
trivially d-closed, but ∅ is not d-closed in K5, since
δ(K5)=δ(∅)=0.

**2. Strictness referee.**
The theorem genuinely requires strict d-closed successor
inclusions, not merely weak self-sufficiency. In K4
a singleton has δ=2 and is strong in K4, but not d-closed,
since δ(K4)=2. A weak-strong chain could therefore fail
the intended global strict conclusion.

**3. Successive and arbitrary finite stages.**
From U_n≤d U_{n+1} and strict transitivity, any earlier
U_n is d-closed in U_m for n≤m. This provides stage
monotonicity without separately assuming it. The
proof of contains_finite uses the coverage hypothesis
and maximum of finitely many stage indices.

**4. Scope toward the C_F generic.**
Global d-closedness of the stage images does not yet prove
the d-closed extension property or genericity of the
countable union. It also does not build the union graph
from the dependent finite tagged carriers. Those require
a coherent reindexing of each finite stage, a fair schedule
of permitted extension requests, and a separate response
proof. The real growth-function class membership and
the required d-closed free-amalgamation hypothesis remain
separate concrete assumptions; they are not consequences
of the abstract chain lemma.

## Independent finite adversarial test

scripts/check_cf_dclosed_chain.py enumerates all labelled simple
graphs of order at most five and all three-rank stage patterns.
Whenever two chronological strict d-closed inclusions hold,
it verifies strict d-closedness of the earliest stage in the
whole finite graph, and checks restriction to every intermediate
ambient vertex set. It reproduces the K4 and K5 missing-hypothesis
controls. This is bounded diagnostic evidence only.

Export the main chain theorems and check their axioms. Mark the
countable d-closed stage consequence GREEN only after a successful
Lean build, standard-axiom audit, placeholder scan and full
regression suite; do not mark countable C_F genericity green
merely from this result.
