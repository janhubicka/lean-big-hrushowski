# Independent Lean audit sources for parallel tracks

1 November 2026.

The workflow previously built only imports appearing in the shared
`CheckAxioms.lean` and ran only that source to audit axioms.
Parallel proof tracks therefore repeatedly changed the same two
shared files: `BigHrushovski.lean` and `CheckAxioms.lean`.
A PR could pass CI and then conflict with `main` purely because
another track appended unrelated declarations.

This patch discovers every `CheckAxioms*.lean` file for both the
module build and the exact axiom/placeholder audit. Track B has its
own `CheckAxiomsCFTrackB.lean`. New Track B Lean files may be
imported there without altering either shared aggregator.

## Adversarial checks

1. **No unbuilt proof:** every `import` line of every discovered
   source enters the Lake target list; a new proof with an omitted
   shared aggregate import still compiles.
2. **No unchecked proof:** the same source set is used for
   `lake env lean`, then passed to
   `scripts/check_axioms.py`. It checks the union of *all*
   exact `#print axioms` endpoints and rejects additional axioms.
3. **Legacy coverage:** `CheckAxioms.lean` still matches the glob
   and retains every existing module and declaration.
4. **Determinism:** bash glob order is deterministic within a
   workspace; `targets` are sorted and made unique. The glob
   is nonempty because the base source remains present.
5. **Placeholder audit:** the existing
   `scripts/check_no_placeholders.py` call is unchanged.
6. **Unrelated regression suite:** the finite model and
   C0/CF regression steps are untouched and must still pass.
7. **Scope:** only CI discovery and one extra axiom source
   change. No mathematical theorem or manuscript marker
   is promoted by this infrastructure patch.
8. **Kernel:** require full integrated Actions CI before merging.

These are internal role-separated checks, not independent human
referee reports.
