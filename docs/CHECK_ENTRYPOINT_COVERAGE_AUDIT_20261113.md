# General Lean CI audit coverage — 13 November 2026

The main `Lean` workflow previously built and axiom-audited top-level
`CheckAxioms*.lean` files only. Track-specific check files named
`CheckTrack*.lean`, `CheckC0*.lean`, etc. could therefore be
left out of the aggregate status despite being the dedicated entrypoints
for new results. Exact-head failures in Track E #508 and #518 were
visible in the dedicated workflows while general Lean was green.

The workflow now uses the existing nonempty glob `Check*.lean` in
**both** its build-target discovery and its `lake env lean` + axiom
audit source loop. The authoritative axiom parser already accepts an
array of source files, accumulates every `#print axioms` declaration,
and admits only `propext`, `Classical.choice`, `Quot.sound`.

## Internal adversarial referee roles

1. **Coverage:** both discovery sites must use identical globs;
   otherwise successful building without checking theorem axioms is
   possible.
2. **Scope:** the glob expands only root-level `Check*.lean` files.
   More deeply nested future checks need either explicit imports or a
   later workflow change.
3. **Source trust:** `check_axioms.py` derives expected declarations
   from the actual files, rather than from a stale hardcoded count.
4. **Negative test:** a dedicated check file absent from the older
   glob now becomes an aggregate build/audit target, detecting missing
   imports, Lean errors and nonstandard axioms.
5. **Compilation:** `BigHrushovski` remains a build target; the change
   adds check modules, not a replacement for the previous root build.
6. **Cost and caching:** more targets can increase runner time.
   This is deliberate; CI green now means more. If the new check fails
   on a stale/dead target, repair or retire that target explicitly
   rather than silently excluding it.
7. **Validation boundary:** this PR changes no mathematical theorem.
   It must pass the *new* exact-head aggregate CI before merge.

This is a role-separated internal critique, not external peer review.
