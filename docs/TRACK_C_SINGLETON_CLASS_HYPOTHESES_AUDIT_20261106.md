# Track C — derive the singleton request from the published class assumptions

Dependent branch built on the pending literal singleton-request PR #315.
The draft is not a replacement for that finite theorem.

## Exact statement

Let F : ℝ → ℝ be monotone and unbounded, with F(0)=0.
Retain the class-level restricted strict d-closed free-amalgamation
property, the paper's independent requirement that the empty
substructure be strictly d-closed in every finite C_F member, and
the numerical consequence F(1)≤2 of the one-vertex graph belonging
to C_F. Then every finite stage of the canonical growth construction
contains a **literal** singleton StageRequest over the empty support.
No separate per-stage nonempty-request or K(0)≥1 assumption occurs.

Proof boundaries: `all_stages_growth` proves stage membership in C_F
using the class free-join hypothesis; the empty-base property is
applied to that stage. The verified exact growth inverse
`cardinalGrowth_inverse` derives 1≤K(0) from F(1)≤2.
The finite parent lemma `singletonStageRequest_exists` then
constructs the actual minimal local type with one fresh ordinal.
Finally `realCountableGraph_unique_of_requests` gives an
induced equivalence of the original birth graph to any Nat graph
satisfying all four strict genericity recognition conditions.

## Internal adversarial referees

- **Class referee:** the stage-growth proof uses restricted free
  amalgamation. Without it, no stage membership follows from the
  growth inequality on local codes alone.
- **Empty-base referee:** ∅≤_d B for all B∈C_F is explicitly
  required, and is not inferred from F(0)=0 or 2-sparsity.
- **Singleton referee:** F(1)≤2 is exactly what the singleton
  graph's predimension inequality says, while F(0)=0 covers
  the empty graph. F(1)>2 is an immediate negative test.
- **Numerical referee:** K(0)≥1 is proved from the exact inverse;
  a separately chosen numerical cutoff or fake nonempty stage
  is not used.
- **Map referee:** the final isomorphism preserves and reflects
  edges on the actual birth vertices. Old source stages are not
  totalized into empty target stages.
- **Certification referee:** compiling the dependency alone is
  insufficient. Exact build plus `#print axioms` for BOTH new
  theorems, on the final PR head, is mandatory.

## Remaining manuscript identification

The comparison graph N is still a parameter and must satisfy
the full finite strict d-closed recognition properties.
Instantiating it with the *published* strong Fraisse limit M_F
is a final semantic bridge, not a theorem asserted here.

The paper's F has nonnegative domain and codomain; this proof uses
the verified real-domain numerical interface. A further exact
specialization by `extendPublishedGrowth` is straightforward
but is not claimed in this PR.

CI pending. These are role-separated internal checks, not an
external panel of independent human referees.
