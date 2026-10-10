# Lean Big Hrushovski

Lean 4 validation of the working manuscript
[The Big Hrushovski](https://github.com/janhubicka/The-big-Hrushovski).

## Certified scope (10 October 2026)

The Lean development now verifies finite graph predimension,
self-sufficiency and closure calculations, tagged strong free
amalgamation of arbitrary finite 2-sparse graphs, finite strong
extension response diagrams, fresh and gap-free initial-segment labels,
and strictly growing finite strong extensions.

It also constructs the union graph of a **given coherent covering
sequence of finite stages** and proves that, if every successor stage
is a strong two-sparse extension, the union is two-sparse, the finite
stages are globally strong, and every finite set has a finite strong
container. The current integrated
[188-declaration Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38079857370)
has only standard logical axioms and no placeholders.

**The countable generic Fraïssé graph is not yet constructed.**
The next theorem must recursively combine each fair-scheduled finite
amalgamation response with strict growth, relabel the resulting stage
as an initial segment, and prove coherence. Only then can the existing
fair-response criterion establish the extension property.

The unary functional closure expansion, the big Ramsey degree
theorems and the Ellentuck results also remain to be formalized.

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
