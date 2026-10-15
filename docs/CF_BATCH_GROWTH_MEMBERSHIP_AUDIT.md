# Adversarial audit — class membership of the actual finite tagged C_F batch

15 October 2026. The conditional theorem is **not** an assumption
that the completed simultaneous stage already lies in C_F. It
derives that conclusion by a finite induction with the following
explicit, independent hypotheses:

1. The original old graph U satisfies δ(X)≥F(|X|) for all X⊆U.
2. Every permitted complete ordered local code satisfies the same
   growth bound in its own finite induced graph.
3. Growth membership is preserved by free amalgamation over an
   intersection that is strictly d-closed in both finite factors.

Hypothesis (3) is the *restricted class-level free-amalgamation
hypothesis* in the published sparse-graph construction. It does
not follow merely from F being monotone and unbounded.

## Four adversarial referee perspectives

**1. Finite class and induced code referee.** A local code must
be a complete member of the class, not only 2-sparse, nor merely
correct on its support boundary. The verified induced-image
invariance of the real growth inequality carries each complete
local code into its actual request-tagged finite image. The
original old stage also retains class membership because its
graph is induced in the tagged construction.

**2. Exact overlap referee.** For an unapplied request r, its
support P_r is d-closed in the current prefix by the tagged-batch
strict closure theorem and transitivity. The complete local
factor E_r=P_r∪B_r is d-closed over P_r by the local minimal
extension theorem. Distinct fresh tags show B_r is disjoint
from the prefix, and the no-cross boundary theorem shows

    Prefix(D) ∩ E_r = P_r.

Thus the class free-amalgamation hypothesis applies over the
*actual* named closed support, not an isomorphic surrogate.

**3. Multi-block referee.** Induction over finite D preserves
the real growth inequality in Prefix(D∪{r}). This covers every
finite subset meeting many different fresh blocks. It is not
enough to check all two-block pairs separately or to use
submodularity without the global class hypothesis. At D equal
to the whole finite request set, the prefix equals the actual
full tagged carrier; therefore the full finite stage belongs
to the growth class.

**4. Missing-hypothesis referee.** For F(n)=n, two triangles
sharing one vertex are each in C_F, and their overlap is
strictly d-closed in both. Their free union has five vertices,
six edges, and predimension 4<5=F(5), so it is NOT in C_F.
Therefore this theorem must retain the separate free-amalgamation
hypothesis. The executable regression also confirms that
the constant F(n)=0 class is closed under small no-cross
d-closed free joins, while arbitrary growth functions need not be.

## What remains beyond the finite class theorem

The Lean theorem is conditional on the published class-level
free-amalgamation property and membership of the selected
allowed local codes. Instantiating those inputs with the
specific growth function and its analytic sufficient conditions
is a distinct theorem (the manuscript already states the
assumption).

Even after finite stage membership and strict d-closedness are
certified, the fair *countable* level schedule, extension
property of the union, identification with M_F, functional
block-root reconstruction, and the embedding-monoid theorem
remain separate formalization tasks.

The independent checker exhausts small finite growth-class
joins and explicitly reproduces the two-triangle counterexample.
It supplements, rather than replaces, the general Lean proof.
Promote the manuscript marker only upon the successful final
CI build, standard-axiom audit, and placeholder scan.
