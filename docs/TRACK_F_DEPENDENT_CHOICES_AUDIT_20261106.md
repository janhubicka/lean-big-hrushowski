# Track F — prefix-dependent finite choice product (6 November 2026)

## Mathematical statement

A succession of finite local choices may vary **as a set** with every
previous selection. If each possible prefix has exactly `g(n)` choices
at stage `n`, the number of complete length-`n` histories is
`prod_{i<n} g(i)`. The proof encodes a complete history by a list;
branches with distinct first elements are disjoint because the
first element can be recovered. The result does not postulate
that different components' *allowable orders* are independent.

This corrects a frequent simplification of the proof of
`thm:N0-exact`: the permitted internal order on a component B depends
on the ordered lower part P_B, but its multiplicity is the fixed
pointwise stabilizer factor g_A(B). The abstract theorem can apply
once we construct the actual prefix-dependent choices and prove
their cardinality from the local code-fibre theorem. That last
specialization and the bijection with global permitted orders
remain **open**.

## Independent adversarial referee roles

1. **History-dependence:** choices vary arbitrarily with the
   complete previous list; no global product of fixed choice sets
   is assumed.
2. **Distinct branches:** lists beginning with distinct choices
   cannot collide even if later allowed sets overlap.
3. **Empty fibres:** zero possible choices at any stage correctly
   makes the total number of histories zero.
4. **Variable-size counterexample:** two initial choices followed
   by branches of sizes one and two yield three histories; a
   constant branch size cannot be removed from the hypotheses.
5. **Certification:** require Lean kernel compilation, standard
   axiom check and independent Python regression before
   declaring any theorem validated. This is internal
   role-separated review, not external human refereeing.

No manuscript prose or validation marker changes. This is a
purely finite counting lemma and does not imply recurrence,
degree one, or any infinite big Ramsey theorem.
