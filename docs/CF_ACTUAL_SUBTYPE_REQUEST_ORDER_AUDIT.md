# Track B adversarial review: exact request order with partial old source

1 November 2026

## Mathematical statement
The selected old map has type `e : SupportCarrier U S → V`, not
`U → V`. For any two actual selected requests `r,s`, the complete
request comparison is preserved **and reflected** by the actual
partial-domain transported request constructor. The ordered key is

1. increasing literal old support;
2. size of fresh block;
3. complete ordered adjacency matrix (edges and nonedges).

This uses the verified complete-code transport in
`CFPartialTagNoncollision`, and the support-lex theorem in the
parent PR #265. It imposes no extra assumption about the global old
source stage or a nonempty target old carrier.

## Role-separated hostile checks

- **Empty-carrier referee.** For `U≠∅, S=∅, V=∅`, a total
  `U→V` does not exist. The subtype map exists; both support
  tuples are empty, so comparison reduces to the size and code.
- **Order referee.** Proper-prefix tuples and comparison at the first
  different support vertex are treated by a strict order embedding
  of the selected subtype. Preservation AND reflection are used.
  Equality of tuples is derived from strict comparison in both
  directions by trichotomy; it is not assumed.
- **Type-code referee.** Equal support tuples do not identify
  requests: fresh size is compared next, then the *complete* ordered
  adjacency matrix. This distinguishes local types even when all
  old supports are the same.
- **Map referee.** The old map remains partial through the proof.
  The ordinal map, simultaneous tagged carrier, inherited
  stage order, and old vertex b-values belong to separate lemmas.
- **Kernel referee.** There is one exact theorem endpoint in
  `CheckAxioms.lean`. The stacked PR must pass full build,
  standard-axiom audit, no-placeholder scan and regressions;
  no green manuscript marker is justified before that.
- **Scope referee.** This theorem does NOT prove a whole one-level
  functional embedding, finite-level induction, uniqueness of
  finite lifts, or the embedding-monoid isomorphism.

## Independent finite regression
An exhaustive enumeration checked **266,981** lex comparisons for
all subsets of selected source sets, all increasing injections into
small target chains (source size ≤ 6), both directions of equality
and strict order, including empty carrier and proper-prefix cases.
All passed. This tests only support-tuple order, not the complete
request theorem nor the Lean proof.

These are independent lines of internal adversarial analysis, not
reports from external human referees.
