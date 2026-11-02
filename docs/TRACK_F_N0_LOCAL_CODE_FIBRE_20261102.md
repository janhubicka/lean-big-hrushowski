# Track F — exact finite local code-fibre cardinality (2 November 2026)

Base: integrated Track F branch commit 76759e31.

## Statement and proof scope

The verified modules \`N0LocalSymmetry\` and \`N0LocalCode\`
already establish that complete matrix-code agreement and
fixed old positions correspond exactly to an orientation
automorphism fixing the old part pointwise. This PR upgrades
that equivalence to a literal equality of finite sets:
\`localCodeFibre P e\` is the image of the pointwise
stabilizer under the map h |-> e.trans h. The map is
injective, so the finite code fibre has exactly
\`|Aut(C)_(P)|\` elements.

Crucially, C here denotes **the finite orientation on which
the theorem is instantiated**. For the manuscript's
\`g_A(B)\`, one must instantiate C with the orientation
induced on \`scl(B)\`, and P with its proper lower successor
part. Counting automorphisms of the ambient orientation
instead would give the wrong value (e.g. the incoming
leaf attached to a directed triangle).

The theorem counts **complete enumerations**, not yet the
set of permitted global vertex linear orders. The
bijection between globally permitted orders and a
component linear extension plus these local fibres
remains separate, as does recurrence and the infinite
degree-one Ramsey theorem.

## Role-separated adversarial checks

- **Full-code reviewer:** records every ordered directed
  edge and nonedge, not only positive adjacency.
- **Old-part reviewer:** uses pointwise rather than setwise
  fixation of the lower successor part.
- **Injectivity reviewer:** composition with a fixed finite
  enumeration is injective on all permutations.
- **Geometry reviewer:** no claim about the ambient full
  automorphism group replaces the induced local group.
- **Certification reviewer:** successful isolated Lean build,
  standard-axiom and placeholder audits are mandatory;
  finite regressions alone cannot certify the theorem.

Companion regression tests every lower-part order in
all 106,264 component closures appearing in the
30,887 orientations of order at most five:
478,199 ordered lower parts and 1,170,649 local
enumerations, all with the exact stabilizer count.
