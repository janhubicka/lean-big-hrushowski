# Track F — the exact inverse for complete tagged SCC-order histories

14 November 2026. Stacked on the Track F integration branch
(PR #270) after the merged, Lean-checked unconditional tagged-history
count (#533). The TeX manuscript and its validation marks are unchanged.

## Statement

Let \(r\) be any consecutive ranking of the actual strongly connected
components of a finite orientation \(A\). For each component \(B\),
choose an enumeration \(e_B:\operatorname{Fin}(|B|)\simeq B\) of its
*labelled* vertices.

The construction \`taggedPrefixFromAssignment\` records these chosen
enumerations for the first \(n\) components in \(r\)-order. Its list is
reverse chronological, matching \`N0TaggedHistoryCount\`. The theorem
\`ordersFrom_taggedPrefix_at_rank_lt\` proves that executing this list
by the existing dependent \`withComponentOrder\` update recovers the
original order \(e_B\) of every component with \(r(B)<n\).

At the full number of components, this gives the literal identity

\[
  \operatorname{ordersFromReverseHistory}
  (\operatorname{taggedPrefixFromAssignment}(r,\mathbf e,m))
  =\mathbf e.
\]

This is a **surjectivity statement for unrestricted assignments**.
It is not the desired bijection between *reachable canonical*
histories and *canonical* assignments; their compatibility remains
a separate proof obligation.

## Adversarial panel — role-separated mathematical checks

1. **Chronology referee.** A new tag is prepended to the stored
   reverse-chronological list but applied *last* when executing.
   This is essential even for repeated updates of one component.
2. **Dependent-carrier referee.** A tag consists of a genuine SCC
   \(B\) and an element of the type of enumerations of exactly \(B\).
   No common permutation type or copy of an isomorphism class appears.
3. **Prefix referee.** The reconstruction statement concerns
   precisely \(r(B)<n\), and deliberately says nothing about
   the unchosen components beyond the rank prefix.
4. **Uniqueness referee.** The component ranking is a bijection
   onto a consecutive finite ordinal. Thus only one component
   occupies each rank and the new update cannot overwrite an
   earlier chosen component in the induction.
5. **Boundary referee.** The empty component set and the empty
   rank prefix are legitimate and must be covered by the same
   proof without a nonemptiness assumption.
6. **Count referee.** Reconstruction of a complete assignment
   alone does not imply that the history is *reachable*. The
   minimum-code predicate at every component must be checked
   using the canonical-prefix locality theorem (#492).
7. **Formal trust referee.** Exact-head Lean compilation, named
   \`#print axioms\` audit, placeholder scan, and independent
   exhaustive finite tests are required. This is an internal
   adversarial panel, not external independent human review.

## Independent regression

The finite script checks all 653 orientations with at most four
vertices, all SCC rankings (including illegal ones), every
collection of internal SCC orders, and every length of rank
prefix. It confirms exact recovery at all previously chosen
components, full equality at the last stage, and a negative
control distinguishing the chronological order of repeated
updates.

## Remaining endpoint

For every legal \(r\), show (i) a canonical component assignment
gives a reachable complete tagged history, using prefix agreement
with the original assignment; (ii) a reachable history gives a
canonical full assignment, using persistence of the earlier
component conditions under later updates; and (iii) the history
and assignment maps are inverses on those restricted sets.

Together with the Lean-certified unconditional tagged-history
count (#533) and the actual-order data bijection (#488), this
would establish the finite formula
\(\ell(A)\prod_B g_A(B)\) **for the precise finite canonical-order
family defined in the code**. This is not an infinite big Ramsey
degree theorem. Check separately that the manuscript's permitted
expansion convention is exactly that finite family before
promoting any manuscript validation marker.
