# Track C — published-domain countable recognition

The exact manuscript growth function has type
`NonnegativeReal → NonnegativeReal`. We use the already
kernel-checked `extendPublishedGrowth` and the equality
`publishedCardinalGrowth_eq` to specialize the merged Nat
generic-recognition theorem without any independently chosen
growth function on negative real inputs.

## Internal adversarial referee panel

- **Hypothesis referee:** F(0)=0, monotonicity and unboundedness
  are exactly the published numerical assumptions used here.
  Continuity is not needed in the cardinal inverse argument;
  the standing finite class free-amalgamation condition is
  deliberately separate and explicit.
- **Subtype referee:** all finite class and comparison-graph
  inequalities use `publishedCardinalGrowth F`, not an
  unrelated real restriction.
- **Carrier referee:** `ι : ℕ ≃ PublishedBirthVertex F ...`
  is assumed explicitly; it cannot be obtained from countability
  without infinitude. PR #300 addresses the latter conditionally.
- **Finite response referee:** the comparison graph N is only
  recognized when it has the **complete** prescribed finite
  d-closed response property, with induced maps and global strict
  closed images, plus finite covers and empty closure.
- **Certification referee:** the new specialization has its
  own isolated Lean build and `#print axioms`. No manuscript
  marker is promoted before CI and before proving the
  singleton-request existence under the paper hypotheses.

This is internal role-separated checking, not external human
refereeing. Current status: CI pending.
