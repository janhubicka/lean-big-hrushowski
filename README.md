# Lean Big Hrushovski

Lean 4 validation of the working manuscript
[The Big Hrushovski](https://github.com/janhubicka/The-big-Hrushovski).

## Certified scope (14 October 2026)

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

**Strong homogeneity and uniqueness are now Lean-certified.**
The finite joint strong extension theorem and an alternating
back-and-forth construction show that any two countable two-sparse
structures with finite strong covers and the strong extension
property are induced-isomorphic. Every finite globally strong
partial isomorphism of the constructed graph extends to an
automorphism. Hence this concrete graph realizes the strong
Fraïssé limit M₀ up to isomorphism. The merged
[PRs #66 and #67](https://github.com/janhubicka/lean-big-hrushowski/pull/67)
passed the [253-declaration integrated audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38148285916),
with only standard logical axioms, no proof placeholders in 57
Lean files, and the existing finite regression suite.

**Finite closure orbit characterization and the C0 two-edge lemma are
now Lean-certified.** The precise finite strong closure of a generator
set is the set of vertices having finite orbit under its pointwise
automorphism stabilizer; this is **not yet** a Lean proof of first-order
`acl=cl_s`. See [PR #74](https://github.com/janhubicka/lean-big-hrushowski/pull/74).
The two-old-neighbour bound and singleton-minimal-increment conclusion
used in the C0 enumeration have exact finite Lean statements in
[PR #75](https://github.com/janhubicka/lean-big-hrushowski/pull/75).
Its [passing audit](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38237316769)
checked 271 declarations with standard axioms only, scanned 64 Lean
files for placeholders and passed the finite regression suite. That historical checkpoint has since been extended to the
**countable C0 enumeration and its unary closure presentation**.

**C0 milestone (13–14 October 2026).** The countable minimal
strong enumeration, finite ancestry closures, finite unary-closed
strongness, exact component/back-edge embedding equivalence, local
minimality, and free persistence are now formalized. [PR #96](https://github.com/janhubicka/lean-big-hrushowski/pull/96)
certifies finite concatenation of prepared components (390 audited
declarations); [PR #97](https://github.com/janhubicka/lean-big-hrushowski/pull/97)
proves that every finite unary-closed set inherits a minimal-increment
presentation (397 audited declarations, [successful run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38481909334)).
Both integrated runs audited standard logical axioms only and passed
the finite regressions.

**Complete finite dependency and unary-value transfer is now certified.**
[PR #99](https://github.com/janhubicka/lean-big-hrushowski/pull/99)
proves preservation of tagged component dependency closures over a
closed common base (405 audited declarations).
[PR #100](https://github.com/janhubicka/lean-big-hrushowski/pull/100)
proves preservation of the **complete vertex-valued** unary function
under whole-block image hypotheses and unary closedness of every
existing finite C0 enumeration prefix. The
[successful 411-declaration CI run](https://github.com/janhubicka/lean-big-hrushowski/actions/runs/38486803292)
audited only standard logical axioms, scanned 88 placeholder-free
Lean files, and checked 121,104 complete block-value equalities.

**Still open in Lean:** identifying strong closure with first-order
model-theoretic algebraic closure, instantiating the tagged closure
results for every finite functional amalgamation diagram, and
constructing the **fair countable functional extension schedule**
on M0; also the CF functional presentation, big Ramsey-degree
arguments, and concrete Ramsey-space axioms required for the
Ellentuck results. The abstract Milliken and Todorčević libraries
can be reused once the appropriate concrete coding and axioms
are formalized.

## Shared C0 / CF finite predimension lemma

The [local free-extension transfer module](docs/LOCAL_FREE_TRANSFER.md)
collects the same no-cross calculation used in the two enumeration
arguments. Under an explicit closed-support boundary for a fresh block,
it identifies weak strongness, strict d-closedness, and minimal-strong
steps before and after freely adjoining a larger old graph.
The strict d-closed endpoint lemmas were certified in
[PR #121](https://github.com/janhubicka/lean-big-hrushowski/pull/121);
the common interface and proof cleanup are in
[PR #122](https://github.com/janhubicka/lean-big-hrushowski/pull/122).

The **minimal d-closed step equivalence** is proved in the manuscript
from the intermediate-set predimension identity, but is not yet an
exact Lean theorem. More importantly, the common lemma does not imply
simultaneous preservation of both complete C0 unary functions, the
countable functional reduct theorem, or any C_F level/monoid theorem.
Those remain separate tasks.

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
