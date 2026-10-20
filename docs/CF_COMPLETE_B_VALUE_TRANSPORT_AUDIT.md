# Adversarial audit: complete b-values and H-value transport

20 October 2026. Scope: `CFBirthBValues.lean`.

## Mathematical claims

For an actual C_F birth vertex v at level n with request tag r, the auxiliary complete set-valued function is exactly
`b(v) = birthSupport(n,r) ∪ birthBlock(n,r)`.
This must not be abbreviated to the fresh block alone or to the graph neighbourhood. The finite-set predicate `IsBirthBlockClosed` is equivalent to requiring `b(v) ⊆ S` for every v∈S.

If a function f maps each complete value on a finite b-closed set T *onto* its target complete value, it sends T to a finite b-closed set. Under full induced adjacency and injectivity, the verified finite globally d-closed hull naturality then yields
`f[H(S)] = H(f[S])` for every finite S⊆T.

## Nine distinct hostile mathematical checks

1. **Full-values check.** The old named d-closed support is included in b(v), even when it contains vertices that are not directly adjacent to v. A mere block or neighbour-set homomorphism is insufficient.
2. **Tag check.** Every fresh ordinal of a given request has *the same complete b-value*. Different requests are never conflated, even when abstractly isomorphic.
3. **Two directions check.** `IsBirthBlockClosed` must be equivalent to saturation of the full b-value at each selected vertex; proving only one implication would not support image closedness.
4. **Image check.** Only exact `f[b(v)]=b(f(v))` implies f[T] is b-closed. A one-sided containment f[b(v)]⊆b(f(v)) would be insufficient.
5. **Injectivity check.** Closure of f[T] uses no injectivity; global finite d-hull naturality *does* require an induced injection so that predimension values and nonedges are reflected.
6. **Finite container check.** To transport H(S), T and f[T] must both be b-closed (hence globally d-closed). The new lemma discharges the image-closedness premise from b-value preservation rather than postulating it.
7. **No infinite delta check.** Every hull comparison uses a finite globally d-closed container; the new theorems assign no predimension to arbitrary infinite substructures.
8. **Partial domain check.** The mathematical hull naturality holds for all finite S, but the language's H is defined only for finite subsets of first vertices. This proof does not silently enlarge that domain.
9. **Embedding-boundary check.** Full equivalence of (R,H)- and b-embeddings still requires recovering b-values from R,H (including block order) and preservation/reflection of root status. The current theorem is one nontrivial component, not the final embedding theorem.

All reviews are internally performed as separate adversarial roles, not claimed as independent outside referee agents. The theorem stays unverified until the branch's complete Lean build, exact axiom and placeholder scan, and all regression tests pass.
