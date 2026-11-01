# Track C: integration registry for separately certified results

The individual Track C modules were built in isolated CI and checked
with exact `#print axioms` endpoints. They were merged in PRs
#276, #277, #269, #292 and #291. This integration PR makes
those source files explicit imports of `BigHrushovski.lean`,
and adds 16 exact endpoints to the repository's global
`CheckAxioms.lean` registry.

This is a **certification scope** change only. It adds no new proof
statement, no new mathematical hypothesis and no TeX change.

## Internal adverse-review panel

- **Compilation referee:** no proof is promoted just because a
  placeholder scan finds no `sorry`; the umbrella and the
  isolated source must both compile.
- **Axiom referee:** the global checker permits only standard logical
  axioms. Each new endpoint is listed explicitly, rather than
  importing modules while forgetting their theorem dependencies.
- **Mathematical-scope referee:** the finite response, strict
  back-and-forth and relabelling endpoints are conditional theorems.
  They do not assert the canonical birth carrier is infinite,
  nor identify the full paper's `M_F` without the standing class
  assumptions.
- **Branch-coordination referee:** this PR owns only
  `BigHrushovski.lean`, `CheckAxioms.lean` and this note.
  It is integrated after the individual proofs to avoid concurrent
  edits to the shared registry.
- **Paper referee:** no green manuscript marker should be promoted
  on the strength of this import-only integration.

## CI gate

The repository's existing `Lean` workflow builds
`BigHrushovski` and all imports of `CheckAxioms.lean`, then runs
`scripts/check_axioms.py` and the placeholder scan. An exact
pass on this PR head is required before merge.

The still open PRs #300 (conditional birth infinitude) and
#302 (Nat-pullback generic recognition) are deliberately not
added in this integration: they need independent isolated CI.

This is internal, role-separated checking, not an external human
referee panel.
