# Adversarial audit: the complete old-fresh boundary of a tagged request

16 October 2026

## Exact statement

Fix a finite old graph U, an actual closed-support request r,
an old vertex u, and a new vertex (r,i). The level graph has
an edge u--(r,i) if and only if there is a named support vertex
q ∈ r.support with q.val=u and the complete local graph of r
contains the edge q--i.

This is stronger than the already certified local-code
inducedness: it characterizes adjacency of the fresh block
to **every** vertex of the old stage, including vertices
outside the support. It proves that no old vertex outside
r.support can become an unexpected neighbour.

## Five adversarial mathematical checks

1. **Request identity.** The proof uses the tagged batch lemma
that any edge incident with a fresh r-vertex must come from
the same request r. It must not allow a different request s
with an isomorphic local graph to supply an extra edge.

2. **Both adjacency directions.** The forward direction
recovers the local support vertex and local-code edge.
The reverse inserts exactly that local edge into the actual
batch. The result is an equivalence, so it detects absent
edges as well as present ones.

3. **No old collisions.** Fresh labels are always tagged as
Sum.inr, while every old vertex is Sum.inl. Even an old
vertex whose name matches a local ordinal cannot be
identified with a fresh vertex.

4. **No spurious old-fresh edges.** A copied local graph
over Q together with a larger old set A is an induced
copy of the intended free amalgam only if the new block
has no neighbours in A\Q. The new corollary proves this
directly; it is not an assumption on the input graph or
an incorrect consequence of old-stage d-closedness.

5. **Still not a total extension theorem.** We have not
yet built a map from the entire prescribed source
A⊕B to the countable birth graph or proved equality of
its image with the globally d-closed union of A and
one tagged block. The present lemma is the key boundary
fact for that theorem, not a genericity certificate.

All changes should pass integrated Lean compilation,
standard logical axioms, placeholder scan and an
adversarial proof review before being merged or marked
green in the manuscript. The five checks here are
separate internal hostile mathematical roles, not
external independent referees.
