# Adversarial audit: coherent embeddings between any finite C_F stages

16 October 2026

The previous PRs give one-step old embeddings and birth labels.
This module defines `ascend(n,k)` as the k-fold literal
Sum.inl inclusion and proves:

    ascend(n,k) is injective;
    E_(n+k)(ascend(n,k)(x), ascend(n,k)(y)) iff E_n(x,y);
    birth(ascend(n,k)(x)) = birth(x).

This is the exact iterated coherence needed to define a countable
limit graph by lifting two representatives to a common stage.

Four hostile checks:

1. **Nonedge referee.** The proof composes equivalences of
   adjacency, not mere forward homomorphism implications.
   It therefore prevents spurious new edges among old vertices.
2. **Index arithmetic referee.** Each successor takes the
   carrier at n+k into the carrier at n+(k+1) by Sum.inl;
   the definitions must agree with the actual recursive
   stage construction, not a separately postulated tower.
3. **Identity referee.** The birth map commutes with every
   iterated old embedding. Equality of birth vertices in
   a later stage implies equality of original vertices,
   through injectivity at the original stage.
4. **No premature limit claim.** These lemmas still do not
   construct the adjacency on the countable birth carrier.
   When defining it from finite stage witnesses, one must
   show that *all* choices of common later stages give
   the same answer. Then one can transfer finite
   predimension and d-closedness to the limit.

Use only the exact Lean theorem names after an integrated CI,
axiom audit, and placeholder scan pass. These referee roles
are separated internal mathematical proof audits, not external
independent human certification.
