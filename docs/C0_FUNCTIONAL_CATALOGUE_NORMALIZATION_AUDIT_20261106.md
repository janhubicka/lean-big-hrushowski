# Track A — adversarial review: arbitrary functional extension request encoding

Date: 6 November 2026. All referee roles are independent
mathematical checks within this review, not external referees.

## Exact target

For a finite canonical C₀ stage `s` on `Fin n`, an arbitrary
finite canonical extension `K` on a finite carrier W with
component index `κ:W→Fin r`, and a prescribed induced
functional embedding `f:Fin n→W`, construct a catalogue diagram
with **exact source `s.model`** and target a transported copy
of K on `Fin(card W)`. Both induced graph relations, including
nonedges, and all complete unary values are reflected exactly.
No component-rank preservation is imposed on f.

The output theorem is
`exists_catalogue_diagram_of_functional_extension`.
It uses `FiniteC0.minimalSteps_relabel` and
`canonicalValue_relabel`, already certified in the library.

## Referee 1 — source not replaced

The source of the constructed diagram is definitionally the
given `s.model`. Replacing it by an abstract isomorphic copy
with reordered vertices would break the fair scheduler's actual
source-label map. The diagram embedding is the exact map
`e ∘ f`, where e is the *target* numbering equivalence.
The original stage's labels remain untouched.

## Referee 2 — arbitrary target carrier

The target may be any finite type W. Its `Fintype.equivFin W`
bijection fixes no pre-existing labels; this is fine because
only the source stage has prescribed Nat labels.
The induced graph on the new `Fin(card W)` carrier
is the pullback along the inverse equivalence.
The theorem proves inducedness in both directions.

## Referee 3 — complete unary operation

For every source point x:
`C_T(e(f x)) = e[C_K(f x)] = e[f[C_s(x)]]`.
The first equality is `canonicalValue_relabel`.
The second is the complete-value embedding hypothesis,
and the final equality uses `Finset.image_image`.
This includes all backwards-reachable whole components,
not only one-step old neighbours.

## Referee 4 — minimal strong presentation

The target's original empty-or-minimal component steps are
transported by an induced graph equivalence. No new
predimension calculation, global sparsity assumption or
component-rank alignment is introduced.

## Referee 5 — joint compatibility versus mere graph embedding

The input map must preserve the entire finite canonical
unary function, not just graph edges. This is essential
to be a member of `FunctionalC0Diagram`. The theorem
does not claim that every induced graph embedding can be
normalized into a functional embedding.

## Referee 6 — countable boundary

This module only encodes one *finite* functional extension.
The actual countable limit proof must still show that any
extension over its finite stage is represented by such data
with the stage's current selected witness, and that the
corresponding request remains applicable through later stages.
The eventual-applicability theorem already handles the latter
once the request is encoded. A final finite-to-countable
response transport, using exact old labels and complete
unary values, must still be performed.

No countable model or functional extension property is
assumed or proved by the encoding lemma alone.

## Certification

Dedicated `track-a-c0-catalogue-normalization.yml` workflow:
build the module, audit its exact theorem-axiom endpoint, and
run the no-placeholder scanner. Do not promote the
countable manuscript marker or merge the draft until CI passes.
