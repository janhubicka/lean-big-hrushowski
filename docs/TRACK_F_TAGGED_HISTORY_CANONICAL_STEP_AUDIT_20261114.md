# Track F — persistence of earlier canonical component conditions

14 November 2026. Stacked on PR #543 (exact reconstruction of
unrestricted tagged SCC-order assignments). This file documents an
internal, role-separated adversarial audit; it is not a report
from independent external referees.

## New statements

Fix a *legal* ranking r of the actual SCCs and two actual components
C and B with r(C) < r(B). Replace only the chosen enumeration of B.

The theorem \`canonicalAtComponent_iff_later_update\` proves that
the complete canonical minimum-code condition on the true successor
closure C_C is unchanged. The proof uses the certified rank-prefix
locality theorem from PR #492 and the exact dependent-component update
lemmas. It concerns all directed adjacency-code entries, not merely
arrows between old vertices and C.

The theorem \`mem_canonicalTaggedNextChoices_iff\` unpacks a concrete
member of the tagged next-choice set: the tag is precisely the actual
component of rank \`history.length\` and the attached internal
enumeration satisfies the *original all-generator* canonical
criterion after that component is updated.

These are the two facts needed for an induction showing that
executing a reachable history makes every processed SCC canonical.

## Adversarial referee panel

1. **Order-direction referee.** The component B being updated must
   have *larger* rank than C, since successors are ordered first.
   The theorem does not assert invariance under an update of C
   itself or one of its strict successors.
2. **Full-closure referee.** The canonical test is on the induced
   successor closure C_C, and equality is of complete minimum-code
   predicates, including negative adjacency bits.
3. **Dependent-tag referee.** The next tagged choice is a dependent
   pair carrying an enumeration of the *specific actual component*,
   not an untyped permutation of a common numeric carrier.
4. **Index referee.** Its component is exactly r^{-1}(n), where n
   is the length of the existing history, with the explicit
   n < number-of-components bound.
5. **Typeclass referee.** Equality of actual internal SCC
   enumerations is used via the previously validated
   \`withComponentOrder_other\` lemma; there is no implicit
   transport across an isomorphic but different SCC.
6. **Noncanonical-history referee.** Persistence of an earlier
   predicate does not depend on all other choices being
   canonical. It therefore applies during inductive
   construction of a reachable history.
7. **Certification referee.** Exact-head Lean compilation,
   named theorem-axiom checks, placeholder scan and
   independent complete finite-orientation regressions
   must pass before merging.

## Scope

This PR does not itself claim the finite global degree formula.
The remaining finite integration step is to prove that the
canonical predicate holds at every processed component of a
reachable history and, conversely, that the canonical component
assignment generates a reachable tagged history. The
unrestricted history inverse is submitted in parent PR #543.

No manuscript text or validation markers were modified.
