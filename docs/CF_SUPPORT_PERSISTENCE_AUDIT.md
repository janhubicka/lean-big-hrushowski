# Adversarial audit: persistence of canonical C_F support on free attachment

15 October 2026. The intended finite lemma describes the one-block
step of the proposed level construction, not the countable construction.

Let P≤d A be finite graph vertex sets and let the fresh block B be
disjoint from A. Assume every neighbour of B in A lies in P.
Suppose the local extension P<_d(P∪B) is minimal and its exact local
support is recovered as cl_P^d(N_P(B))=P.

The proposed theorem concludes:
- A<_d(A∪B) is minimal;
- P∪B≤d(A∪B);
- cl_A^d(N_A(B))=P, i.e. the same *actual* old support;
- the no-cross graph amalgam condition on A and P∪B.

## Four adversarial mathematical referees

**1. Relative closure referee.** The equality
cl_A^d(S)=cl_P^d(S) for S⊆P requires P≤d A, not
merely P⊆A. For the forward inclusion, P is one of the
d-closed supersets of S in A. Restriction of the d-closed
hull in A to P makes it a d-closed superset of S in P.
Conversely a d-closed hull in P remains d-closed in A
by transitivity P≤d A. Minimality of each hull forces
both inclusions. This proof needs the *strict* d-closed
restriction and transitivity theorems, not weak strongness.

**2. Boundary referee.** The old neighbours of B are
unchanged only because B has no neighbours in A\P.
The complete old-neighbour set is used, not neighbours
of the first vertex of B. If P=∅, A={a}, B={b}
and ab is an edge, the local old support in P is ∅,
but the old support in A becomes {a}, even though
∅≤d A and the isolated local B is minimal.

**3. Minimality and second-factor referee.** With P≤d A,
the no-cross criterion and the certified minimal-step
transfer give A<_d(A∪B). The strict free-factor theorem
gives P∪B≤d(A∪B). These are distinct conclusions:
neither automatically implies the other. If P≤d A is
omitted, K5 plus an isolated new vertex gives a
counterexample to support recovery and strict closure
of the second factor.

**4. Scope and iteration referee.** This is an exact
one-block statement in a finite graph. It proves
the support is unchanged when the old prefix grows,
which is required before one can identify an extension
block's level and catalogue code. It does not assert
that A∪B belongs to the restricted growth-function
class C_F; this uses the *separate* class-level free
amalgamation hypothesis. It does not yet give the
finite simultaneous attachment or fair countable
stage schedule.

## Independent diagnostic

scripts/check_cf_support_persistence.py enumerates all labelled
graphs of order at most five and every partition into
P, A\P and B. On each diagram satisfying the four exact
hypotheses, it checks all four conclusions. The script
also contains negative controls deleting no-cross and
P≤d A, and cases of multi-vertex minimal blocks.

The test is bounded counterexample search. Exact Lean
certification requires an integrated build, standard-axiom
audit for all three new declarations and a placeholder
scan. Only after this may the manuscript acquire a
green marker for the one-block support-persistence step.
