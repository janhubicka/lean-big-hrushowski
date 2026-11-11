# Track F: minimum complete-code fibre (8 November 2026)

The exact N0 degree formula requires distinguishing a chosen canonical
local order from the complete family of allowed local orders. This
note isolates the missing finite counting assertion.

Fix a finite orientation on C, an old lower part P, and a nonempty
finite family X of complete enumerations of C. Assume:

- **Old positions:** all members of X agree at the positions
  occupied by P; these are precisely the previously ordered
  lower vertices.
- **Full local symmetry:** X contains every enumeration with the
  same complete directed adjacency code as one of its members
  and agreeing with that member at every old position.
- **Complete code:** equality of code values is equivalent to
  equality of the entire directed adjacency matrix, including
  nonedges and the directions of arrows.

For any linear order of the code values, the enumerations in X
with least code form precisely one local code fibre. Hence the
fibre cardinality equals the pointwise stabilizer
`|Aut(C)_(P)|`. This **does not** assume the family X is
independent of earlier component choices; only its size is
constant. Changing the order of codes does not change the
cardinality.

Lean endpoints: `completeDirectedMatrix_eq_iff`,
`minimumCodeClass_is_minimal`, and
`minimumCodeClass_card`. The proof is conditional on X.
Constructing X from each ordered lower successor part in the
manuscript, and proving that all permitted global vertex orders
arise by the staged construction, remain separate tasks.

## Role-separated adversarial referee panel

1. Full-code referee: discarding arrow directions or nonedges
   invalidates the complete-code equivalence assumption.
2. Pointwise referee: if P={0} in two isolated sinks, allowing
   both permutations overcounts the pointwise factor 1 as 2.
3. Orbit referee: if X contains only one of two automorphic
   sink enumerations, its minimum fibre has size 1 instead of 2.
4. Coding referee: a code which artificially distinguishes two
   automorphic enumerations yields incorrect fibre sizes.
5. Dynamic-history referee: X may depend on the ordered lower
   part and earlier choices; the product argument uses the
   separate certified dependent-history lemma.
6. Certification referee: no infinite Ramsey assertion follows
   from this finite theorem; require compilation and kernel
   axiom/placeholder checks before merging.

The independent Python regression checks every two-orientation
on at most four vertices, every fixed old subset P, and all
enumerations fixing P. It also tests the three negative cases.
This panel comprises internal adversarial roles, not external
human referees. No TeX manuscript markers change.
