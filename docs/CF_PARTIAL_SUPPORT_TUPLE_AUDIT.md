# Adversarial audit: sorted named support under partial order maps

29 October 2026

## Claim

For a finite support P and a map f strictly increasing on P,
the increasing tuple of the literal image f[P] is exactly the
pointwise image of the increasing tuple of P. No global order
embedding U → V is required, and f may be arbitrary outside P.

The proof restricts to the finite subtype P and constructs
two genuine order embeddings: the inclusion P ↪ U and the
restriction of f to P. Sorting the full finite subtype
through each embedding gives the same canonical list.

## Separate hostile checks

1. **Proper subsets.** The target image may lie in a smaller
   ambient stage. The proof never extends the embedding of P
   to an order embedding of all U.
2. **Empty support.** When P is empty, the finite subtype and
   both sorted lists are empty; no target inhabitant is needed.
3. **Noninjectivity outside P.** The map may identify unrelated
   old vertices outside P. Strict monotonicity on P alone
   guarantees injectivity on P and prevents loss of named
   support elements.
4. **Different support sizes.** The theorem handles every
   finite P and preserves its entire sorted tuple, so
   proper-prefix comparisons are covered downstream by
   the existing partial-source lex theorem.
5. **Exact code scope.** This discharges the named support
   tuple equality in the request transport certificate when
   the target support is literally f[P]. The fresh-size and
   full adjacency-matrix equalities remain separate inputs.
6. **Lean verification.** Three exact axiom endpoints are
   registered. Full build, standard axiom audit, placeholder
   scan and finite regressions must all pass before
   promoting the theorem.

These are adversarial mathematical checks within the project,
not independent external human referee reports.
