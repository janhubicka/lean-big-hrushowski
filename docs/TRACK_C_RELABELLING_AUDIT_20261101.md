# Track C — graph relabelling bridge: internal adversarial audit

## Exact statement

The user-visible manuscript builds a countable graph on labelled birth
vertices; our existing uniqueness lemma is currently formulated on ℕ.
This PR proves a generic bridge *conditional on an actual equivalence*
`e : U ≃ V`:

- `GraphOn.globallyDClosed_pullback_iff`: for the exact induced graph
  `G.pullback e`, a finite set is globally **strictly** d-closed
  precisely when its image is globally strictly d-closed in G;
- `finiteDClosedCover_pullback`: the finite globally closed-container
  property transfers without assuming a canonical enumeration;
- `finiteGrowth_pullback`: the complete finite cardinality growth
  inequality is preserved on every finite subset.

This branch does **not** claim an equivalence ℕ ≃ the C_F birth
carrier: a countable carrier might be finite. Establishing its
infinitude from the paper's singleton and free-join assumptions is
an independent obligation.

## Role-separated adversarial reviewers (internal)

- **Predimension referee:** the proof uses the induced *bijection*,
  not merely injectivity, in the global closure direction; finite
  predimensions are identical via `predim_image`.
- **Closure referee:** every proper finite extension is considered.
  Neither weak self-sufficiency nor closure relative to one finite
  stage substitutes for global strict d-closedness.
- **Cardinality referee:** the injective map preserves every Finset
  cardinality. No estimate on F beyond the stated inequality is used.
- **Relabelling referee:** the inverse equivalence supplies exact
  preimages of arbitrary finite target supersets, including the empty
  and nonempty cases.
- **Certification referee:** the stated three declarations, not a
  general umbrella build, are the isolated `#print axioms` endpoints.
  No published-paper validation marker is promoted before CI.

Status: branch created, isolated CI pending. This is internal
role-separated adversarial review, not external human refereeing.
