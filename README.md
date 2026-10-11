# Lean Big Hrushovski

Lean 4 validation of the working manuscript
[The Big Hrushovski](https://github.com/janhubicka/The-big-Hrushovski).

## Certified scope (11 October 2026)

The Lean development verifies finite graph predimension,
self-sufficiency and closure calculations, tagged strong free
amalgamation of arbitrary finite 2-sparse graphs, finite strong
extension responses, gap-free initial-segment labels, and strictly
growing finite strong extensions.

**The unconditional countable strong generic graph is now
machine-certified.** The proof constructs a coherent, strictly
growing sequence of finite two-sparse graph stages on consecutive
initial segments of ℕ, answering each applicable fair-scheduled
finite strong extension and using an empty strong request to force
growth otherwise. The union has nonnegative predimension on every
finite set, finite globally strong covers, and the full labelled
strong extension property. This was checked in
[PR #48](https://github.com/janhubicka/lean-big-hrushowski/pull/48),
whose [passing Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38087807401)
checked 212 declarations with only standard logical axioms, scanned
45 Lean source files for placeholders and passed the finite
regressions, including 2,337 growing strong response diagrams.

The constructed graph is also **strongly universal** for the finite
two-sparse class: every finite two-sparse graph on an arbitrary
finite vertex type has an induced globally strong copy. This
corollary was certified in
[PR #52](https://github.com/janhubicka/lean-big-hrushowski/pull/52),
which audited 215 declarations and checked 47 Lean files for
placeholders.

**Still open:** formalizing strong homogeneity and uniqueness by
finite strong back-and-forth, thereby identifying the constructed
graph with the specific strong Fraïssé limit M₀ of the manuscript.
The complete functional closure presentations, big Ramsey-degree
arguments and the concrete Ramsey-space axioms for the Ellentuck
results also remain to be formalized.

## Reusable libraries

See [FORMALIZATION_DEPENDENCIES.md](FORMALIZATION_DEPENDENCIES.md)
for precise interfaces to
[`lean-milliken`](https://github.com/janhubicka/lean-milliken)
and
[`lean-ramsey-space-todorcevic`](https://github.com/janhubicka/lean-ramsey-space-todorcevic).
They contain verified abstract theorems; concrete Ramsey-space
axioms and a compatible `lean-successors` pin will be required for
downstream import.

## Build and audit

```sh
lake exe cache get Mathlib.Tactic Mathlib.Data.Finset.Basic
lake build BigHrushovski
lake env lean CheckAxioms.lean > axioms.log
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean
python3 scripts/check_no_placeholders.py
```

The exact statement ledger and independent finite regression
references are in [VALIDATION.md](VALIDATION.md), with adversarial
failure-mode checks in [ADVERSARIAL_REVIEW.md](ADVERSARIAL_REVIEW.md).
