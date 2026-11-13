# Track F — preserving old successor positions under a top-SCC change
13 November 2026

Base: Track F integration branch, after merged #492, #497 and #500.
No manuscript text or validation markers are modified.

## Statement and role in the counting proof

Fix a legal ranking r of the actual SCCs, a complete family of chosen
internal SCC enumerations, and an actual SCC B. For x in B put
C=C_B and P=P_B=C\B. Replace only the enumeration of B by any
other bijective enumeration of its *same labelled vertices*.

The module \`N0StageOldPositionInvariance.lean\` proves:

1. The resulting assembled global orders agree on all comparisons
   between vertices outside B (no legality assumption on r).
2. The proper lower part P_B is an initial segment of either order
   *restricted to C_B*, provided r is legal.
3. All comparisons within P_B agree before and after replacing B.
4. By the merged initial-segment lemma #500, the two complete
   enumerations of C_B put every old vertex in P_B at the same
   **absolute ordinal position**.
5. Two different orders of B yield complete C_B enumerations with
   the same old positions, regardless of whether those choices are
   canonical.

This supplies the first half of the missing identification between
the concrete next-component choices of #497 and the canonical
fixed-old-position fibre of #413/#473.

## Independent adversarial referee panel

1. **Scope of old part.** P_B is an initial segment of C_B, not
   necessarily of the ambient V. The regression constructs a legal
   global order (2,1,0) with an edge 0→1 and an unrelated singleton 2,
   where P_B={1} is *not* ambient-initial.
2. **Pointwise versus setwise.** Equality of the set P_B is not
   enough. The conclusion fixes each old vertex at the same
   numerical position in the complete C_B enumeration.
3. **SCC identification.** From x∈B, the proof explicitly uses
   \`component x=B\` to show that no vertex of P_B belongs to B.
   Undirected connectivity is insufficient.
4. **Within-SCC comparisons.** When two old vertices lie in one
   SCC other than B, the chosen enumeration of that component
   is preserved literally by the update.
5. **Between-SCC comparisons.** When they lie in distinct SCCs,
   the fixed SCC ranking determines their order independently of
   local vertex ranks, including when they are nonadjacent.
6. **Dependencies.** The legality hypothesis is used only for
   the lower-part initiality, not for arbitrary comparisons
   outside B. Reversing a source-successor ranking is a negative
   control.
7. **Certification.** The exact named Lean declarations are
   audited for standard axioms; a placeholder scan and an
   independent small finite test must pass. The role-separated
   audit is internal, not external peer review.

## What remains

For an arbitrary complete enumeration f of C_B fixing the old
positions, let t be the labelled order it induces on the actual
top SCC B. Prove that updating B to t in the global SCC assembly
recovers precisely f on C_B. This surjectivity uses the already
certified component assembly comparison theorem, the old-position
invariance proved here, and the finite enumeration uniqueness
theorem.

Once that inverse is kernel-certified, the map from the *entire*
fixed-old complete enumeration set to internal orders of B is
bijective. Restricting to the lexicographically minimum complete
code class gives exactly g_A(B) admissible next choices.

The uniform-dependent-history lemma (#482) and actual canonical-data
cardinality result (#488) then prove the finite product formula,
subject to the explicit identification of reachable histories
with full canonical assignments. The infinite N₀ big Ramsey theorem
remains a separate proof obligation.
