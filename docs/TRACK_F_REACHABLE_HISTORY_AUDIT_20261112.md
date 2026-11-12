# Track F — dependent counting on reachable histories (12 November 2026)

This is a finite counting preparation for the N₀ ordered-expansion
formula. It changes **no manuscript text or validation markers**.
It is based on the Track F integration branch (PR #270).

## Main statement

Let \`choose : List α → Finset α\` specify the possible next
choices from a history (stored most recent first). Let \`H_n\`
be the finite set of length-n histories reachable from the empty
history by successive permitted choices.

If for every reachable \`h ∈ H_n\` the next-choice set has
cardinality \`g(n)\`, then

\[
  |H_n| = \prod_{i=0}^{n-1}g(i).
\]

The choice sets themselves may vary with the history, and the
condition is needed only for reachable histories. This strengthens
the usability of the earlier \`FiniteDependentChoiceCount.histories_card\`,
whose uniformity hypothesis ranges over *all* prior lists.

Proof: partition \`H_{n+1}\` by the tail of the history. The pieces
are disjoint because deleting the new head recovers the previous
history. Each piece has cardinality \`g(n)\`. Finite induction
gives the product.

## Independent adversarial referee panel

1. **Reachability referee.** The induction must use only histories
   in \`H_n\`. It must not invoke the fibre hypothesis on arbitrary
   lists. The Python negative test gives a reachable singleton
   stage-one history with two choices but an unreachable stage-one
   list with no choices.
2. **Multiplicity referee.** Distinct choices extending a fixed
   history give distinct new histories. The proof uses injectivity
   of \`List.cons\`, not an assumed disjointness of choice sets.
3. **Overlap referee.** Distinct prior histories give disjoint
   images under extension even when the same new value appears
   as a choice for both. This is checked by taking list tails.
4. **Zero referee.** Empty choice fibres are allowed, and a zero
   factor makes all later reachable sets empty. The theorem
   must not assume that \`g(n)>0\`.
5. **History referee.** Previous choices occur in a list, not
   an unordered set. Their complete order matters for the
   canonical lower successor part.
6. **Uniformity referee.** The number of next choices is
   assumed uniform, not their identity. For N₀ the
   stabilizer-cardinality theorem is expected to supply that
   uniformity after the local top-order restriction is
   identified with the genuine next-component choices.
7. **Certification referee.** Named Lean axiom checks,
   placeholder scan and an independent finite enumeration are
   required at the exact head. These internal, role-separated
   checks do not constitute human external peer review.

## Remaining interface

This purely combinatorial theorem **does not identify** the
reachable histories with actual globally permitted orders.
That requires a finite bijection between the correct successive
component-choice fibres (over each previously ordered lower part)
and the canonical top-component orders. The latter are already
counted by \`N0CanonicalTopOrderFibres\`; the bridge remains open.
The infinite N₀ Ramsey theorem is separate.
