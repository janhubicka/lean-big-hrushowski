# Adversarial audit: C_F tagged comparison equals the inherited stage order

30 October 2026

## Exact claims

The literal successor-stage order is the same as the named-code
comparison: old vertices retain their old order and precede all
fresh vertices; fresh vertices are compared by the full
support-tuple/fresh-size/complete-adjacency key of their requests,
then by their chosen finite ordinal.

The selected-block map built from actual transported requests
preserves and reflects this order between actual source stage n+1
and target stage m+1, for **arbitrary** n and m, including m < n.
The map is only defined on selected old vertices and selected
complete blocks. It does not assume an embedding of the whole
old stage n into stage m.

## Role-separated hostile checks

1. **Order referee.** Fresh/fresh comparisons must use the precise
   request order rather than a convenient arbitrary numbering.
   The previously verified equivalence between canonical numerical
   ranks and the literal request codes is used. Equality of ranks
   is reflected to equality of request tags by the verified
   rank injectivity theorem.

2. **Old/fresh referee.** All four comparisons are checked, including
   the impossible fresh-before-old case; the latter uses
   asymmetry of the actual linear order, rather than assuming
   a total preorder suffices.

3. **Partial-source referee.** The selected map is defined on S
   and on fresh blocks whose supports are in S. Its order
   preservation uses strict monotonicity on S alone. No order
   embedding of the complete source U_n into U_m is required,
   so the result applies when m < n.

4. **Lean/axioms referee.** The linear orders on U_n and U_m are
   constructed recursively, and must be explicitly supplied
   to the actual target request construction. A prior CI run
   exposed missing instance arguments and an incomplete
   injectivity application. They are now explicit in the
   theorem and its proof. Three exact axiom endpoints are
   registered; a full build, standard axiom audit, placeholder
   scan and finite regressions are required before promotion.

5. **Scope referee.** This is an order theorem for a single
   simultaneous selected level. The complete graph-inducedness,
   injection, and strict d-closedness are already verified in
   earlier modules, but the complete block-support operation
   and iteration through the represented levels still need
   further work. The finite unique level-lifting and
   embedding-monoid conclusions are not asserted.

These are role-separated mathematical adversarial checks within
the project; no independent external human referees have been
consulted for this change.
