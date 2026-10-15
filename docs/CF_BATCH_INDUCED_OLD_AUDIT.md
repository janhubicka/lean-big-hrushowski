# Adversarial check: induced old graph and exact batch boundaries
15 October 2026

The new theorems in CFBatchInducedOld.lean are finite graph claims about
the previously certified *actual* simultaneous request-tagged graph.

**Referee 1 — inducedness versus positive edge preservation.**
The old-tag inclusion must preserve both edges and nonedges.
Although the batch definition includes all original old edges,
other local codes can introduce further old-old edges unless their
induced bases agree pointwise with the actual old graph. The proof
uses each request's exact base_agrees field. It does not rely merely
on disjointness of fresh tags.

**Referee 2 — several codes sharing an old support.**
The same old pair may occur in arbitrarily many locally isomorphic
requests. These codes may be copied more than once, but every old-old
adjacency agrees with the single old stage G. Thus no amount of
duplication adds a forbidden old edge. Distinct *fresh* copies remain
disjoint from PR #141.

**Referee 3 — full support boundary.**
An old endpoint adjacent to a new vertex of the block r must lie
in the literal support r.support, not merely in an isomorphic
copy of that support. The proof uses the tag's exact request
identity and the subtype membership proof for the old vertex.
This excludes every crossing edge from a fresh vertex to
an old vertex outside that request's actual support.

**Referee 4 — no false closure claims.**
Inducedness of the old graph and the correct old-neighbour
boundary still do not establish that each entire normalized
local graph is an induced subgraph: new-new edges and exact
indices must also be reflected. Moreover, pairwise one-block
d-closure is not a proof that U is d-closed in the whole
simultaneous union. Membership in the growth-function class
C_F must still be supplied by its concrete free-amalgamation
theorem, not inferred from the pure predimension library.

The existing independent regression
scripts/check_cf_tagged_simultaneous.py checks exact old induced
adjacency and every old-to-fresh boundary for all 122 small
request copies. The Lean theorems above are the general
certificates for those two parts of the regression.
The remaining induced local-code and strict batch closure
steps will be formalized separately.
