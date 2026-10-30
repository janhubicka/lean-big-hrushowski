# Adversarial audit: sorted literal supports under partial C_F maps

30 October 2026

## Claim

Let S be the selected old finite carrier and let P,Q⊆S be
literal supports. The map e:S→V is strictly increasing, but need
not be defined on the complete source old stage U. The sorted
tuple of each source support is recovered by sorting its
representation in the subtype S and forgetting the subtype.
The sorted tuple of its literal target image is obtained by
mapping the same subtype tuple through e.

Consequently the usual strict lexicographic comparison of P
and Q is preserved and reflected by e, including proper-prefix
comparisons. The result is independent of predimension or of
the particular C_F growth function and is a reusable finite
linear-order lemma.

## Hostile checks

1. **Empty-target:** The case S=V=∅ with nonempty U is legal.
   No total function U→V, nonempty target or dummy target
   vertex appears. When P and Q are empty their sorted
   subtype tuples are empty and neither strict comparison
   holds.

2. **Literal names:** The selected support is the actual
   finite set of old subtype vertices, not an isomorphism
   class of finite subgraphs. Forgetting the subtype gives
   the original support P exactly. Applying e gives the
   actual named target support e[P].

3. **Order:** The map e is strictly increasing on the
   selected subtype. Both the inclusion S↪U and e:S↪V
   are strict order embeddings. The previously verified
   list-lex transport theorem preserves and reflects
   unequal lengths and proper-prefix comparisons.

4. **Finite lists:** Sorting is applied to exact finite
   sets before mapping. The proof uses the previously
   verified sort-image lemma and does not assume that an
   arbitrary injection preserves sorting.

5. **Scope and kernel:** The theorem proves only strict
   support-tuple comparison. Equality of complete
   request codes and comparison of their fresh sizes
   and adjacency matrices must be combined separately.
   Five exact axiom endpoints are recorded. Full build,
   standard axiom audit, placeholder scan and finite
   regressions must pass before any green marker is added.

These are separate internal adversarial checks, not
independent human referee reports.
