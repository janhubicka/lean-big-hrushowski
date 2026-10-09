# Lean Big Hrushovski

Formal validation of the working manuscript [The Big Hrushovski](https://github.com/janhubicka/The-big-Hrushovski).

First target: the finite graph predimension, submodularity, and self-sufficiency
lemmas. This is NOT yet a verification of the whole manuscript. The exact
statement correspondence and remaining gaps are recorded in VALIDATION.md.

Setup follows partite-construction with its pinned Lean and Mathlib versions.

Build and audit:
    lake exe cache get Mathlib.Tactic Mathlib.Data.Finset.Basic
    lake build BigHrushovski
    lake env lean CheckAxioms.lean > axioms.log
    python3 scripts/check_axioms.py axioms.log CheckAxioms.lean
    python3 scripts/check_no_placeholders.py
