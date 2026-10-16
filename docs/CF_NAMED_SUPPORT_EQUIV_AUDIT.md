# Adversarial audit: canonical named support equivalence

16 October 2026

## Exact finite statement

Let P⊆A be the canonical old support of a finite minimal
strict d-closed extension and suppose a prescribed induced
embedding of A into a finite target stage is supplied as an
injective map e defined on the subtype carrier of A.

The *actual image* Q=e[P] is a finite vertex set in the
target. Restrict e to the subtype of P. Its image lies exactly
in the subtype of Q, and the resulting map P→Q is bijective:
injectivity is inherited from e; surjectivity holds by
definition of Q. The induced embedding of A therefore
restricts to an induced graph equivalence between the
graphs on P and Q.

This equivalence is canonical from the specified e. It
does not select an unrelated isomorphic support or extend
e arbitrarily to the fresh vertices outside A.

## Five independent hostile mathematical checks

1. **No total-extension assumption.** The original
embedding is only defined on the finite old source A,
not on all vertices of a later finite extension C.
The proof must not demand an injection of all C into
the current finite stage U_n, since that would assume
the desired extension already exists.

2. **Literal image.** Q is built from the attached vertices
of P and their images under e. The subtype equivalence
is onto *this exact set* by definition, rather than
an arbitrarily chosen support isomorphic to P.

3. **Injectivity and collisions.** Since e is injective
on A, two distinct vertices of P cannot be identified
in Q. The map's subtype injectivity is proved via
injectivity of e, not inferred from mere graph
homomorphism properties.

4. **Full inducedness.** The map is used with a two-way
adjacency equivalence on A. This ensures preservation
of nonedges and all finite predimension calculations,
not merely edges, on the designated support.

5. **Precise remaining bridge.** This theorem supplies the
missing old-support equivalence for PR #166. It does
not itself transport the fresh local graph or prove
the size bound K, nor extend e over the requested
minimal increment. Those are separate already
formalized or outstanding obligations.

All exact endpoints must pass final Lean CI with
standard-axiom and placeholder checks before any
manuscript marker is made GREEN. The five roles above
are separated internal adversarial proof checks, not
outside human referees.
