# Track D: Uniform finite local orders via top-permutation orbits (8 November 2026)

## Finite statement

Let (D,E,C) be a permitted finite one-generated C0 structure.
Put B(D)={b in D:C(b)=D} and P(D)=D\B(D).
The existing finite hereditary proof gives B(D) nonempty,
P(D) closed under the COMPLETE unary values, and C(b)=D for all b in B(D).
No vertex of B(D) is distinguished as generator.

Assume that P(D) has an *already selected locally coherent order*:
for every x in P(D), the restriction to C(x) is the ordered local
type previously selected. It is essential to include this condition;
the statement is false for an arbitrary order on the lower part.

**Proposition (English proof; not yet Lean-certified).**
For every ordered local datum (D,P(D),<P) satisfying this inductive
hypothesis, one can select an ordered ISOMORPHISM TYPE extending <P,
putting all of P before B, invariant under isomorphisms preserving
the ordered lower part, and compatible with every one-generated
restriction to C(x) for x in D.

**Proof.** Induct on |D|. Since B(D) is nonempty, |P(D)|<|D|.
Keep the increasing enumeration of the ordered lower part P.
For every permutation of the top component B, append those vertices
to P and record the COMPLETE binary matrices

    A(i,j) = [ E(d_i,d_j) ],
    F(i,j) = [ d_j in C(d_i) ].

The resulting finite set of binary words is nonempty. Select its
lexicographically least word. Two minimizing enumerations yield the
same full incidence matrices, hence matching equal positions gives
an induced ordered (E,C)-isomorphism. An isomorphism of the original
local data fixing the order of P maps top enumerations bijectively,
so the sets of binary words and their minima agree.

For x in P, complete closedness implies C(x) is contained in P,
so the induced order on C(x) has not changed and is correct by the
inductive hypothesis. For x in B, C(x)=D, so its ordered closure has
precisely the newly selected type. These cases cover D. QED.

**Automorphism warning.** The least word can have several minimizing
enumerations, related by automorphisms of the unordered local structure.
The construction selects one ordered isomorphism TYPE, not a raw order
preserved by all automorphisms. Choosing the order of B from the raw
vertex names is not invariant under renaming.

## Five-vertex adversarial boundary (new)

The conditional proposition above is valid, but it must **not** be
misread as a globally renaming-invariant assignment of physical vertex
orders obtained by processing components one at a time with raw-name
tie-breaking. There is already a counterexample in the actual sparse,
minimal-strong finite C0 age.

Take five vertices 0,1,2,3,4, all six edges among 0,1,2,3, and only
the additional edge 1--4. The component chain is

    empty < {0} < {0,1,2,3} < {0,1,2,3,4}.

Every increment is minimal strong for predimension
delta(X)=2|X|-|E(X)|, and all induced subsets have delta >= 0.
The complete unary closures are C(0)={0},
C(1)=C(2)=C(3)={0,1,2,3}, C(4)={0,1,2,3,4}.

In the middle stage, the top component {1,2,3} is symmetric over
the lower part {0}; all six top enumerations give the SAME complete
matrix, so lexicographic minimization of that matrix does not choose a
unique physical enumeration. A secondary tie-break by raw names gives
(1,2,3). Relabel the same graph by swapping names 1 and 3. The raw
tie-break still gives (1,2,3), but now vertex 4 is adjacent to 3,
not 1. Consequently the resulting complete ordered code of C(4)
is different. The earlier <=4-vertex exhaustive check did not cover
this five-vertex obstruction.

**Correct conclusion:** for a *specified* ordered lower part P, the
minimum complete matrix defines a unique ordered ISOMORPHISM TYPE
extending P. Transporting that supplied order through an isomorphism
gives the same minimum. It does not select a canonical underlying
bijection or a physical order commuting with all unordered
automorphisms, and it cannot enforce relabel-invariance of a stagewise
arbitrary tie-break in larger presentations. The resulting distinct
orders of P in the two presentations represent distinct *ordered*
lower-part data; neither violates the conditional induction statement.

The exact negative control is now in
`scripts/check_c0_local_order_normalizer.py`: it verifies all three
minimal strong steps and sparse predimensions, exhibits inequality
of the raw-tie global codes, and checks equality of the conditional
local codes after transporting the lower order. Any later
`W` construction must use ordered local types as its keys, not
silently identify arbitrarily chosen physical orders.

## Formalization boundary

- BigHrushovski/C0CoordinateTopPermutationOrbit.lean is submitted on
  PR #332. Its proposed theorems give a finite nonempty orbit of complete
  edge/unary matrices under permutations fixing all ORDERED lower
  positions pointwise, invariance under a top permutation, and orbit
  equality iff a top permutation matches the complete matrices.
- The uniform ordered-lower-part induction above is proved here in
  English, NOT yet instantiated in Lean for the full C0 finite age.
  The missing step identifies the actual local types with the
  top-permutation orbits and constructs a coherent choice globally.
- scripts/check_c0_local_order_normalizer.py additionally exhibits the genuine five-vertex raw-tie obstruction above, and exhausts 1,401 finite
  minimal-strong presentations on at most four vertices, 5,545
  local codes and 130,289 comparisons under ALL relabellings.
  It includes four non-singleton increments and a raw-label-order
  counterexample. These are finite tests, not kernel verification.
- Even after local selection, the countable host W, unique finite
  coordinate lifting, the return embedding psi, and recurrence
  remain separate obligations.

## Six internal adversarial checks

1. FULL LANGUAGE: both edges/nonedges and all complete unary memberships
   are encoded; positive-edge maps do not suffice.
2. STRICT INDUCTION: B is nonempty, P is C-closed, and |P|<|D|.
3. ISOMORPHISM INVARIANCE: preserve the ORDERED P, not only the raw P set;
   candidate top matrices then give the same set of words.
4. NO FALSE RIGIDITY: an unordered automorphism need not preserve any
   selected linear order; only an ordered isomorphism type is chosen.
5. EVERY GENERATOR: separate x in P and x in B; no named top generator
   is built into the representative.
6. CERTIFICATION: an English argument plus exhaustive tests is not a
   Lean proof. Keep PR #332 draft and manuscript validation markers
   unchanged pending exact-head kernel audit and the remaining age bridge.

The review is internally role-separated, NOT external human refereeing.
