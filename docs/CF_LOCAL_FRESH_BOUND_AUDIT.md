# Adversarial audit: actual local fresh-block size bound

16 October 2026

## Exact statement

Let H be a finite graph on S⊕B, let P⊆S be the canonical
literal old support, and suppose the induced interval

   P.image Sum.inl <_d P.image Sum.inl ∪ actualFresh S B

is a minimal strict d-closed growth-class extension.
Let F be the growth lower bound and K satisfy the inverse
property F(m)≤2(k+1) ⇒ m≤K(k).

The certified finite minimal-growth-size theorem bounds
the whole endpoint by K(|P|). The entire fresh block is a
subset of that endpoint, so its size is no greater.
For any injective old map f:S→U we have |f[P]|=|P|,
giving the exact bound expected by the named response:

   |B| ≤ K(|f[P]|).

This is a typed bridge: P is a Finset S, its image in H
is P.image Sum.inl, and its actual named target support is
P.image f. No arbitrary relabelling of P is introduced.

## Five independent hostile proof checks

1. **Whole endpoint.** The numerical theorem bounds
the *whole* minimal extension P∪B. It is incorrect
to use the inequality directly on B as though B were
itself a minimal d-closed substructure. The new
statement uses only the subset cardinality inequality.

2. **Fresh witness.** The every-generator size bound needs
a fresh vertex b∈B. The theorem includes b:B explicitly.
For an actual minimal proper extension, such a vertex
exists; removing that requirement prematurely could
make the theorem false for an empty fresh type.

3. **Literal cardinalities.** Images under Sum.inl and
Sum.inr are injective; hence their cardinalities are
|P| and |B|, respectively. The final target image f[P]
has the same cardinality as P because f is injective.
These are separate equalities, not definitional casts.

4. **Growth hypothesis.** Membership in C_F must hold
for the induced finite local endpoint to apply the
growth-size bound; monotonicity of F alone is not enough.
The current theorem assumes the full finite H satisfies
the growth inequality and restricts it to the endpoint.

5. **Final composition.** This proves only the numeric
fresh-size bridge. The canonical old support, split
local graph certificates, actual named ordered code,
complete boundary match and globally d-closed response
remain distinct proof steps. No genericity conclusion
is inferred here.

Each of the five checks is an internal adversarial
mathematical review, not an external independently
spawned referee. The exact theorem must pass full
Lean CI, standard logical-axiom checks and no-
placeholder scan before being marked verified.
