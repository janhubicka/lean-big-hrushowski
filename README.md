# Lean Big Hrushovski

Lean 4 validation of the working manuscript
[The Big Hrushovski](https://github.com/janhubicka/The-big-Hrushovski).

## Certified scope (10 October 2026)

The Lean development now verifies finite graph predimension,
self-sufficiency and closure calculations, tagged strong free
amalgamation of arbitrary finite 2-sparse graphs, finite strong
extension response diagrams, fresh and gap-free initial-segment labels,
and strictly growing finite strong extensions.

The formalization now also proves that **a uniform finite fair
successor-existence theorem suffices to construct** a coherent,
strictly growing sequence of finite stages whose union is two-sparse,
has a finite strong cover and satisfies the labelled strong extension
property. This implication is certified in the
[207-declaration Lean audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38086764663),
using only standard logical axioms and no proof placeholders.

**The unconditional countable generic Fraïssé graph is not yet
machine-certified.** The missing premise is the existence of a
strictly growing, gap-free Nat-labelled strong successor that answers
every applicable scheduled request, with an empty strong-request
fallback otherwise. The proposed concrete proof is being checked
in [PR #48](https://github.com/janhubicka/lean-big-hrushowski/pull/48).
It must pass the complete build and axiom audit before this README
can claim the generic has been formally constructed.

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
