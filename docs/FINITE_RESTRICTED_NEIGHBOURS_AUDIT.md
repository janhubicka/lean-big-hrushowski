# Adversarial audit — finite restricted old-neighbour transport

22 October 2026

## Statement

Let f:U→V be any map and C a finite source vertex set. Suppose
for all u,v∈C, adjacency in G is equivalent to adjacency of
their images in H. For A,B⊆C, the image of *the whole set*
of neighbours of B among A is exactly the neighbour set of
f[B] among f[A]:

  f[N_A^G(B)] = N_{f[A]}^H(f[B]).

No global inducedness or injectivity of f is required.

## Hostile referee checks

1. **Only local hypotheses.** The map may behave arbitrarily
   outside C. In particular, it need not be a global self-embedding.
2. **Both adjacency directions.** Forward preservation is
   insufficient: target neighbours not present in the source
   would break the reverse equality.
3. **Complete B set.** Neighbours of the entire block are used,
   not merely neighbours of its distinguished first vertex.
4. **No injectivity used.** If f identifies vertices, the equality
   of neighbour images still holds under exact pairwise adjacency
   equivalence; injectivity is required later for d-hull images
   and set differences, not this identity.
5. **Images of A and B.** Each target neighbour in f[A] and f[B]
   has explicit witnesses in A and B, so the reverse direction
   does not assume surjectivity on the whole target graph.
6. **No growth hypotheses.** The theorem is valid for arbitrary
   simple graphs, and can be reused for C_0 and C_F.
7. **Source subtype use.** A graph embedding of a finite closed
   source supplies this exact condition when restricted to A∪B.
8. **No automatic support equality.** Transporting neighbour sets
   alone does not recover a d-closed support; the finite induced
   hull transport theorem must also be applied.
9. **Kernel check.** The exact declaration is listed in CheckAxioms;
   complete build, placeholder and downstream regression checks
   are required before GREEN status.

These are role-separated internal hostile reviews, not external
human referees.
