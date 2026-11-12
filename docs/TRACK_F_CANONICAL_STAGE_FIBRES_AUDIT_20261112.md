# Track F — actual canonical next-SCC extension fibres (12 November 2026)

Base: Track F integration PR #270, with previously certified
component assembly and induced-closure canonical fibre theorems.
No manuscript or validation-marker changes.

## Definitions and finite theorem endpoints

A complete SCC-order assignment is a dependent family of bijections
\(e_B:\mathrm{Fin}(|B|)\simeq B\), for the actual strongly connected
components B of a finite orientation.

The new module \`N0CanonicalStageChoices.lean\`:

- Gives a fixed arbitrary complete assignment to fill components
  which have not yet been selected.
- Defines \`withComponentOrder\`, changing only one actual
  component B while fixing every other component enumeration.
- Proves the updated value at B is exactly the chosen enumeration
  and every other component retains its previous value.
- Proves that distinct choices for B give distinct complete
  assignment records, without quotienting by automorphisms.
- Defines \`IsCanonicalAtComponent\`, the complete local code
  predicate for all generators of that actual SCC.
- Identifies the existing global canonical assignment condition
  with the conjunction of all these component conditions.
- Defines \`canonicalNextComponentChoices\`, the **actual finite
  set** of new orders of B satisfying the local canonical test.
- Shows the corresponding set of updated whole assignments
  has precisely the same cardinality as that set of local orders.

The crucial still-unproved endpoint is

\[
  |\operatorname{Next}_r(\mathbf e,B)|=g_A(B)
\]

for every *legal* SCC ranking r and every reachable prior history.
The present theorem establishes only the equality of the
two concrete representations of this next-choice set.
The local factor theorem of merged #473 suggests the required
cardinality but does not alone supply this identification.

## Internal adversarial referee panel

1. **Actual component referee.** The new order is a bijection
   with the original vertex subtype B, not with an isomorphic
   abstract component or a made-up ordinal block.
2. **Update referee.** Changing B must not alter the enumeration
   stored at any other component. The exact value and inequality
   cases of the dependent function update are checked separately.
3. **Collision referee.** Different internal enumerations of B
   yield different complete assignment records. Failing to keep
   labels would invalidate the next-fibre cardinality.
4. **Whole-code referee.** The canonicality test is on the
   complete induced successor closure C_B, including arrows
   and nonarrows, not merely on the top SCC B.
5. **Generator referee.** The local predicate checks every
   vertex in B, avoiding any hidden dependence on an arbitrary
   representative until invariance is explicitly proved.
6. **Uniformity referee.** The correct stabilizer cardinality
   is not postulated as a Lean theorem here. The independent
   finite test checks it exhaustively but cannot certify the
   general case.
7. **Certification referee.** Exact-head Lean compilation,
   named theorem axiom audit, placeholder scan and exhaustive
   finite tests must pass before the PR is merged. The present
   role-separated checks are not external peer review.

## Independent finite regression

All orientations of at most four labelled vertices are
enumerated. For each legal SCC ranking, each complete assignment
of internal SCC orders, and each current component B, the test
changes only B and computes the complete induced adjacency
code on C_B. It counts exactly the changes which produce
lexicographically minimal code among all enumerations fixing
the observed positions of P_B.

The test compares that count with the *induced*
\(|\operatorname{Aut}(A[C_B])_{(P_B)}|\) for every context.
A directed triangle supplies a negative control: six possible
internal orders but only three canonical code-minimizers.
The result is finite evidence; the general Lean statement
remains open.

## Next mathematical step

Prove that for every legal ranking, changing only B does
not change the already ordered positions of P_B in the induced
C_B order; identify the local candidate set with the canonical
top-component order fibre in merged #473. The prefix-locality
theorem in PR #492 provides independence of later components.
Together these results should establish uniformity of every
reachable next fibre. Then the reachable-history count (merged
#482), combined with the actual canonical data bijection
(PR #488), gives the finite product formula.
