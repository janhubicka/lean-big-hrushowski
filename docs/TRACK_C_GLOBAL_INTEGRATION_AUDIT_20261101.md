# Track C — integrated global certification (1 November 2026)

This PR is an **integration-only** replacement for superseded #307.
That PR's full Lean workflow passed, but the main branch had moved
as other proof tracks concurrently edited `BigHrushovski.lean`
and `CheckAxioms.lean`, so GitHub refused the stale merge.
The current branch starts from the new main and retains every
other track's imports and axiom declarations, then adds Track C.

## Exact integrated scope

Eleven already merged and isolated-CI-certified modules are added
to `BigHrushovski.lean` and 22 exact theorem endpoints to
`CheckAxioms.lean`. This includes:
- published nonnegative-domain F and complete finite response;
- the real canonical countable birth graph certificate and
  literal induced finite-subtype response;
- global strict d-closed back-and-forth and finite joint steps;
- global strict closure and growth under carrier equivalence;
- conditional infinitude of the birth carrier from actual
  requests at each finite level;
- countable genericity of the canonical graph after an actual
  Nat equivalence, under the published F hypotheses.

Every declaration was previously checked in its isolated workflow
at merged PRs #269, #276, #277, #291, #292, #300, #302, #311.
The new integration itself must pass the **full project build
and global axiom audit** on its exact head.

## Internal adversarial panel

- **Integration referee:** source ownership is confined to the
  two shared root audit files and this documentation; previously
  merged parallel-track work is preserved in full.
- **Hypothesis referee:** no singleton-request existence is
  assumed to follow from monotonicity or unboundedness alone.
  The actual request hypothesis in #300 and exact genuine
  equivalence in #302 remain explicit.
- **Strictness referee:** weak self-sufficiency is not substituted
  for global strict d-closedness in any countable recognition
  endpoint.
- **Semantics referee:** the published strong limit M_F has not
  been explicitly instantiated as a comparison generic.
  Importing conditional uniqueness is not a proof of the
  entire manuscript Lemma CF-finite-level.
- **Certification referee:** a passing umbrella build checks
  the listed declarations and their imports; it does **not**
  certify an unlisted high-level English claim. Do not promote
  a manuscript green marker from this integration alone.

Still open: #312 combines the actual birth-carrier conclusion,
#315 constructs the literal singleton request, and their
subsequent class-hypothesis specialization. These modules are
intentionally not imported until exact isolated verification.

This is internal role-separated adversarial checking, not a
panel of independent external human referees.
