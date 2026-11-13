# Track F — reachable histories of actual tagged SCC orders
13 November 2026

Based directly on the Track F integration branch, using the already
certified reachable-history lemma #482 and actual next-component
choice-set definition #497. No manuscript text or validation markers
are changed.

## Finite statement

Fix an SCC ranking r. Different SCCs have different finite
labelled vertex types, so the possible internal order at B is
a genuine bijection \(\mathrm{Fin}(|B|)\simeq B\). To place all
these choices into one history type, the module uses the
dependent tag

\[
  (B,t),\qquad B\in \mathrm{SCC}(A),\quad
  t:\mathrm{Fin}(|B|)\simeq B.
\]

A history is a list of these tags with the newest choice first.
Reversing it and applying the actual dependent update
\`withComponentOrder\` to the fixed default assignment gives
a complete family of local orders.

At stage n, the next component is exactly \(r^{-1}(n)\).
The finite set of possible tagged next choices is the image
of the *actual* canonical next-component choice set from
PR #497. There are no choices after all SCCs are processed.

The new module \`N0TaggedHistoryCount.lean\` proves, conditionally
on the exact uniformity of the *actual* next-choice sets at
every complete context,

\[
  \bigl|H_m(r)\bigr|
  =\prod_{i<m}g_A(r^{-1}(i)).
\]

The uniformity hypothesis is stronger than the reachable-only
hypothesis used in the proof; once the actual stage count is
certified, it holds for every context and therefore suffices.
The **sets** of choices may depend on the entire previous history.

The proof uses the certified \`FiniteReachableHistoryCount\`
induction. It does not identify distinct SCC fibres by a
common carrier or quotient any labelled orders by automorphisms.

## Internal adversarial referee panel

1. **Dependent carriers.** Each tag records the actual SCC B and
   an internal enumeration of B, not a numeric permutation
   obtained by arbitrarily relabelling the component.
2. **Correct chronological order.** The history is stored newest
   first; it is reversed before executing updates. The next
   stage is determined by the *length* of the actual history.
3. **No collisions.** Two different internal B orders give
   different Sigma tags for the fixed B. This justifies
   the cardinality of the tagged image.
4. **Boundaries.** There are no choices at stage n≥m. The local
   factor function is zero beyond the actual number of SCCs.
   The theorem only uses the product through m.
5. **Real choice sets.** The next choices come from
   \`canonicalNextComponentChoices\`, the exact labelled
   component-order set defined and validated in #497.
6. **No premature global bijection.** The Lean theorem counts
   reachable tagged histories. The claim that these are in
   bijection with globally canonical assignments is a
   separate final integration obligation, not implicit.
7. **Certification.** Exact-head Lean build, standard-axiom
   audit, placeholder scan and an independent finite
   chronological regression are required; this is an
   internal adversarial panel rather than external review.

## Independent finite regression

The script enumerates all 653 orientations on at most four
vertices, every legal SCC ranking, and every *reachable*
prefix of permitted tagged component orders. At each stage
it checks the induced stabilizer count, the correct component
tag, and the product cardinality.

At the end it assembles each full history into a labelled
global order, checks uniqueness, and compares its image with
an independent enumeration of all globally canonical orders
having that precise SCC ranking. The expected total across
all small structures is 1,764 canonical labelled orders.
This is **computational evidence**, not a Lean proof of
the final global identification.

## Remaining mathematical interface

For each legal ranking r, prove that the finite reachable
history set H_m(r) is in literal bijection with
\`canonicalAssignmentsAtRanking r\` from #488. One
direction reads a full assignment in rank order and shows
that each choice was accepted by the corresponding genuine
next-stage predicate. The other folds the accepted tagged
history into the full assignment and uses prefix locality
(#492) to show every component remains canonical after
later choices.

The final uniform choice cardinality is submitted through
#510, #517, #519 and the explicit bridge #528.
Once those are certified and the history-to-assignment
bijection is formalized, #488 yields the finite product
formula for actual canonical labelled orders. This alone
will not prove the infinite N₀ big Ramsey theorem.
