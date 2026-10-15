# Adversarial audit: each local CF code is induced in the tagged batch
15 October 2026

The theorem CFStageCatalogue.levelGraph_local_adj_iff asserts, for
every request r and every pair of vertices of its complete ordered
local code, that adjacency holds in the simultaneous tagged graph
**if and only if** adjacency holds in the original code. The
consequence levelGraph_local_minimal_image transfers the exact
minimal strict d-closed step to this finite induced image.

## Four mathematical referees

**Old-old referee.** An edge between two old vertices may be
contributed by the global old graph or by *any* local request
whose support contains both vertices. These relations coincide
because every complete local code agrees with the actual
induced base graph. The already certified levelGraph_old_iff
handles both positive edges and nonedges.

**Fresh-endpoint referee.** Every edge incident to a fresh
vertex tagged r can only be contributed by local code r:
neither the old graph nor a different tagged code has such an
endpoint. One must prove the equality of the contributing
request, rather than assume it merely because the two
local types are isomorphic. Injectivity of localTag then
identifies the precise original local endpoints.

**Within-block referee.** A local code may have several fresh
vertices and edges among them. Its graph is not determined
only by the support mask. The new induced theorem quantifies
over all pairs, including fresh-fresh, old-new and old-old;
the independent checker additionally compares every
finite induced predimension value for each local copy.

**Relative minimality referee.** Induced graph equality
allows us to transport the exact minimal d-closed extension
over the copy of the code's named support *inside that
copy's finite image*. It does not assert that this local
support is d-closed in the **whole simultaneous level**,
nor that the full old graph is d-closed in that level.
Proving those statements requires a separate finite
multi-block closure argument. The restricted C_F class
membership and fair countable schedule are still open.

The existing tagged-batch checker is expanded to compare
every subset predimension of each local copy and test its
minimal strict d-closed step, in addition to the old-edge,
complete adjacency and boundary regressions. The Lean
theorems and the strengthened executable check must pass
the standard-axiom and placeholder audits before any
manuscript marker becomes green.
