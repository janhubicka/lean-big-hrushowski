# Track F: finite induced orientation audit (2 November 2026)

This module is deliberately independent of the one-component lower
part construction being developed in a separate dependent PR.

\`OrientationInducedFinite.lean\` defines the orientation induced on
an arbitrary finite vertex set s. The complete directed adjacency
matrix on s is preserved and reflected. If s is successor-closed,
every outgoing neighbour of every x in s belongs to s, so the
induced orientation has exactly the complete original outgoing
sets at all selected vertices. No such assertion is valid for an
arbitrary nonclosed subset.

This is the correct bridge for evaluating the local symmetry group
\`Aut(C_B)_(P_B)\` inside the induced orientation on C_B, rather than
mistaking it for a subgroup of the full ambient graph automorphisms.
No automorphism group count or big Ramsey conclusion is proved
by this finite restriction module alone.

Internal adversarial checks:
- Directed rather than undirected adjacency is compared.
- Nonedges are reflected because the induced relation is defined
  by filtering the entire outgoing set.
- Out-degree cannot increase when restricting.
- A nonclosed source singleton in x->y loses its outgoing
  edge and therefore cannot preserve the full unary S-operation.
- Directed cycles cause no exception to the induced construction.
- A fresh Lean build and standard-axiom/placeholder audit are
  mandatory before calling the module certified.

Independent exhaustive regression checks all 977,655 vertex sets
of the 30,887 2-orientations on at most five vertices.
