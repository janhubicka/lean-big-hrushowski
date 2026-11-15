# Track F — every canonical assignment has a reachable tagged history

14 November 2026. Stacked on PRs #543, #547 and #551.
No manuscript, TeX or validation-marker changes.

## Proposed finite theorem

Fix a legal ranking r of the *actual* strongly connected
components of a finite orientation and a complete family of
labelled internal component orders \(\mathbf e\) satisfying
the complete canonical code condition at every component.

The deterministic tagged history
\(\operatorname{taggedPrefixFromAssignment}(r,\mathbf e,n)\)
lists the first n components in rank order, newest tag first.
The new module \`N0CanonicalAssignmentReachable.lean\` proves:

- At each stage n, its executed assignment agrees with
  \(\mathbf e\) at every component through rank n, so the
  canonical test at \(B=r^{-1}(n)\) holds.
- The next tag is therefore an actual member of the previously
  defined \`canonicalTaggedNextChoices\`, not a synthetic
  numerical surrogate.
- By induction the tagged rank-prefix history is reachable at
  every n, and its complete history executes back to
  \(\mathbf e\) exactly (using PR #543).

Consequently every genuine canonical component assignment
has **at least one** reachable complete tagged history.
The theorem does *not* assert uniqueness; this is the last
independent condition for a full finite bijection.

## Internal adversarial referee panel

1. **Reachability referee.** Full canonicality is not
   enough to assert a history is reachable without checking
   each chronological next-choice membership. This is the
   induction's main mathematical obligation.
2. **Prefix referee.** The canonical test at rank n can
   depend on previously chosen SCC orders in \(P_B\), but
   not on future SCC orders. The proof invokes the
   rank-prefix locality theorem (#492), not independence
   of the sets of local choices.
3. **Actual-tag referee.** Each tag is a dependent pair
   carrying the original component B and its actual
   enumeration. Other components with equal cardinality
   cannot be silently substituted.
4. **Direction referee.** The stored history is newest
   first; its execution reverses that list, so the
   top component is updated after its lower successors.
5. **Generator referee.** The proof uses the complete
   all-generator canonical component predicate already
   certified in the earlier modules. No chosen-generator
   shortcut or unproved conversion is necessary.
6. **Count referee.** Surjectivity of the history execution
   onto the canonical assignment set does not prove
   injectivity or equality of cardinalities. The latter
   is deliberately not claimed.
7. **Certification referee.** Require exact-head Lean build,
   named standard-axiom audit, no-placeholder scan, and
   exhaustive finite regression including the empty
   orientation. These are internal challenge roles, not
   independent external peer reports.

## Independent finite test

For every orientation with at most four labelled vertices,
every legal SCC ranking and every complete internal
assignment, select those assignments whose complete
induced C_B adjacency codes are all canonical. Read
their component orders chronologically from the ranking
and verify that each update meets the actual next-component
canonicality condition. The regression expects 1,764
canonical assignments over all 653 orientations.

## Remaining finite theorem

Show that a reachable complete tagged history is uniquely
determined by its executed component assignment. One can
prove the stronger prefix statement: for every reachable
history h of length n, reading from its executed assignment
the first n SCC orders in ranking order recovers exactly h.
The update at stage n has a new component r^{-1}(n), so it
never overwrites any earlier component.

With this injectivity, PR #551 supplies the map from
reachable histories into canonical assignments, the
present PR supplies surjectivity, and PR #533 gives the
rank-specific product. The exact finite canonical-order
data correspondence (#488) then yields
\(\ell(A)\prod_B g_A(B)\) for that *specific* finite
expansion definition. The equivalence of that definition
with the paper's permitted orders and the infinite Ramsey
statement must still be audited separately.
