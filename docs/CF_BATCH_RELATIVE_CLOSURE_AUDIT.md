# Adversarial audit — every finite C_F sub-batch is d-closed in the full stage

15 October 2026

## Statement and significance

Let U be the old finite stage and let R be its complete finite set
of permitted ordered local requests. Their actual tagged finite
graph was constructed and its strict d-closedness U≤d U' certified.

The new, stronger theorem asserts that for **every** subset D⊆R,

    U ∪ ⋃_{r∈D} B_r ≤d U ∪ ⋃_{r∈R} B_r.

The conclusion holds even for arbitrarily chosen, nonconsecutive
request tags and for intermediate vertex sets meeting many omitted
blocks. It is the missing finite factor closure needed when a
particular extension is realized by just one block while every
other request is attached at the same level.

## Four mathematical adversarial perspectives

**1. Relative starting-prefix referee.**
The earlier induction started with U. Here the initial prefix
contains an arbitrary set D of already attached blocks. We must
show that attaching *any disjoint* finite family E of additional
requests preserves d-closedness of the starting prefix, not
just that U remains d-closed. Each new r∈E is absent from the
current prefix because its request tag is not in D∪(E\{r}).

**2. Actual support and boundary referee.**
At each induction step P_r≤d U≤d current prefix; both inclusions
are strict finite d-closed relations. The new tagged block is
disjoint from the prefix, and every neighbour it has there belongs
to its literal old support. These are the exact hypotheses of
the already certified one-block support-persistence theorem.
It is not enough that the old supports are abstractly isomorphic.

**3. Finite-global strictness referee.**
Strict transitivity gives d-closedness of the original arbitrary
prefix in the enlarged prefix after each new block. For D arbitrary,
take the additional set R\D, which is disjoint from D; their
union is all R, whose tagged prefix is the entire carrier. This
proves the global finite claim and in particular the single-block
prefix U∪B_r≤d U'. Pairwise weak strongness would not imply it;
strictness must hold for every intermediate vertex set.

**4. Class-membership and countable referee.**
The result concerns the finite graph's predimension.
The separate conditional theorem for membership in C_F uses
the **restricted** class-level free-amalgamation hypothesis.
Neither that finite class theorem nor this arbitrary-prefix
strict-closure theorem constructs a coherent countable stage
sequence or proves the fair extension property. Root functions
and the embedding monoid remain further distinct tasks.

## Independent executable regression

The actual tagged graph checker has been strengthened. For every
small finite level, it samples *arbitrary, noninitial* sets of
completed request tags. It compares the predimension of each
resulting partial prefix with the predimension after adjoining
one, two, or several fresh vertices of omitted requests,
including subsets that cross many different blocks. It also
retains the already exhaustive local adjacency, exact support
and chronological minimality regressions.

This bounded diagnostic is not a substitute for the Lean proof,
which quantifies over all finite intermediate sets. The new
theorem may receive a green validation marker only after the
integrated build, standard-axiom audit, placeholder scan and
regression all pass at the exact final PR head.
