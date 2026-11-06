# Track F: complete local adjacency code versus pointwise stabilizer

Date: 1 November 2026. Separate dependent proof branch off PR #270.

The manuscript's local canonical order for a component B is obtained
from the lexicographically least complete directed adjacency code
on C_B=P_B union B, after the order of P_B is fixed. It is essential
that all outgoing arrows are recorded (not merely positive adjacency
or a chosen numbering of the two outgoing neighbours).

The new \`N0LocalCode.lean\` proves:
- Two enumerations e,f of a finite oriented graph have identical full
  adjacency matrices iff the permutation e.symm.trans f is a digraph
  automorphism.
- The two enumerations agree at every position of P iff this
  permutation fixes P **pointwise**.
- Both conditions together hold exactly when f is the transport of e
  by one of the pointwise stabilizer permutations.
  This is an equivalence of predicates on actual complete bijections,
  not an unproved cardinality assertion.

The companion main Track F branch proves that the orbit of transported
enumerations has cardinality |Aut(C_B)_(P_B)|. Together these statements
give the precise finite matrix-code/stabilizer dictionary. A remaining
step must identify such enumerations with unique **linear-order
relations** on C_B and then prove independence across a component
linear extension. This PR does not certify the product formula for all
permitted orders, recurrence, or the infinite big Ramsey degree.

**Adversarial review:** 83,291 finite enumeration comparisons over
3,577 successor-closed lower parts in 653 orientations verify the
complete code equivalence. A fork with two sinks admits a permutation
swapping the sinks which preserves all arrows but does not fix the
old lower part pointwise. This directly rules out an incorrect
setwise-stabilizer replacement. The empty oriented structure is
included. A passing Lean build and exact axiom audit are mandatory
before this new finite correspondence is marked verified.


## Additional adversarial round

The independent regression now uses up to 24 distinct source enumerations per orientation of size at most three and three different source enumerations for four vertices, then compares all target enumerations. For each of 252,115 pairs it constructs the actual change-of-enumeration permutation and checks full directed adjacency agreement against orientation automorphism, and old-position agreement against pointwise fixation. All checks passed; the initial Lean compile was repaired by removing an invalid orientation-qualified prefix on the orientation-independent `SameLowerPositions` predicate. Kernel certification remains subject to the next successful CI run.
