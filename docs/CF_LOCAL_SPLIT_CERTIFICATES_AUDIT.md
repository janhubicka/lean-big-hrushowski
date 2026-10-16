# Adversarial audit: C_F local split growth/minimality/support transport

16 October 2026

The canonical old-support theorem gives an actual P⊆S for a minimal
finite strict d-closed extension on S⊕B. Its three local facts are
initially expressed in the original complete graph on the finite
vertex interval P.image Sum.inl ∪ actualFresh S B.

The new module makes the *complete induced* local graph on the
literal split carrier {s:S//s∈P} ⊕ B explicit, and transports the
three premises needed by the named one-step response:

  1. exact C_F growth membership for every induced finite subset;
  2. minimal **strict** d-closedness of the old subtype in the
     entire local split graph;
  3. equality of the old subtype with the strict d-closed hull
     of all its old neighbours of the fresh block.

This uses the canonical injection of P⊕B into S⊕B. Its image
is exactly P∪B, not an arbitrary subgraph or induced copy
with different support names.

Five adversarial proof reviews:

**A. Nonedges and growth.** An edge-preserving homomorphism would
not preserve δ or the C_F growth predicate. The local split graph
is the exact pullback of the whole finite graph under an injective
map, so all nonedges, including cross-boundary nonedges, are
reflected. The growth predicate is transferred with the
already certified growthSparse_image_iff theorem.

**B. Correct finite image.** The old part maps onto precisely
P.image Sum.inl; the fresh part maps onto exactly actualFresh S B;
their complete union is the image of the full local carrier.
No old/fresh collision or missing old neighbour may be silently
ignored.

**C. Minimal strict closure.** The local minimal-step image theorem
must be applied in the right direction. Its source is the
complete induced local graph, and its target is the original
finite ambient graph restricted to exactly P∪B.
It cannot be replaced by weak self-sufficiency.

**D. Exact old-neighbour hull.** The old-neighbour set is
transported through the same full induced injection as the
graph, and its least d-closed hull must map onto the exact
support. Just preserving the set P without its hull would
not yield a well-formed actual local request.

**E. Remaining size/response.** The split certificates do
not derive a numerical growth inverse or construct the
complete countable embedding. They are intended for
composition with the literal named support, size bound and
already certified named one-step response. No whole-genericity
statement is implied by this single theorem.

This audit uses five intentionally separated internal hostile
mathematical checks, not independent external human referees.
Green annotation requires final complete Lean compilation,
standard-axiom report, and no-placeholder scan.
