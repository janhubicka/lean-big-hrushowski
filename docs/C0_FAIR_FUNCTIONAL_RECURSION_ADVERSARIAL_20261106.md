# Track A — adversarial audit: actual finite fair recursion

Date: 6 November 2026. Scope: `C0FunctionalFairRecursion.lean`
stacked on `C0FunctionalFairSuccessor.lean` (PR #334).
Referee roles are internal mathematical reviews, not independent
external human agents.

## Claim and scope

Beginning with the explicit empty canonical finite graph on `Fin 0`
and its unique empty component index, choose a strictly growing
finite canonical functional successor for every step of the
fair request schedule. The recursive sequence is defined by
`Nat.rec` and `Classical.choice` from the proven finite existence
theorem. The exact successor certificate used for that choice is
accessible to all later proofs. It establishes:

- a strict numerical increase at **every** step;
- eventual coverage of every Nat-labelled vertex and every finite set;
- induced strong preservation of old graph edges, nonedges and complete
  unary values, fixing all old numerical labels;
- a strong induced complete-functional response to the scheduled
  request whenever that request applies.

These are finite-stage properties. This file does **not** yet
construct the countable graph/unary limit or show every request
applicable in the final limit is eventually answered.

## Adversarial referee 1 — data extraction from propositions

The record of a finite successor contains an actual map
`old : Fin n → Fin m`, so it must retain that map as data.
Its existence is represented by
`Nonempty (Σ t, IsFairFunctionalSuccessor step s t)`.
`Classical.choice` yields an actual successor paired with
its data; `Nat.rec` takes exactly the first projection.
The second projection is the literal certificate for the
same successor, not a second unrelated choice.
This avoids attempting to project computational data
from a `Prop`-valued record.

## Adversarial referee 2 — empty base

The start uses `emptyFinGraph` on `Fin 0` and the only map
`Fin 0→Fin 0`. Every minimal-component obligation on an
index below zero is vacuous. Forced-growth fallback ensures
the first actual successor has at least one vertex.

## Adversarial referee 3 — recurring requests

The scheduler `fairFunctionalC0Request` is already certified
to revisit every finite labelled functional request after
any specified threshold. The selected sequence only proves
that **when** the request is applicable it is answered at
that step. Applicability of an embedding already present
in the countable limit at a later finite stage is a separate
eventual-applicability lemma and is not assumed here.

## Adversarial referee 4 — exact numerical coverage

Strict size growth on *consecutive* finite ordinals implies
that every natural number appears, not merely that infinitely
many distinct vertices appear. The proof reuses
`FiniteSpan.initialSegment_stages_cover`; finite-set
coverage follows by monotonicity and finite induction.
A construction with arbitrarily skipped Nat labels would
not suffice.

## Adversarial referee 5 — strongness and closure fidelity

The stage-step certificate carries a strong embedding and
full equality of old unary values, not only graph inducedness.
The later graph/unary limit bridge must apply the *same*
numerically fixed source maps to define coherent old-old
adjacency and stable finite-valued operations.
The present theorem `fairStages_old_strong` is over the
actual chosen old map and new finite graph.

## Adversarial referee 6 — remaining theorem

A fair recursive sequence is **not** automatically a
functional Fraïssé limit. To identify its graph reduct
with `M₀`, one must build the coherent countable graph
and entire finite-valued unary function, transport literal
finite canonical presentations, and prove the full
functional-stage extension property from the labelled
schedule (including arbitrary finite target relabelling).
Then the already verified `C0CountableStageFunctionalExtension`
and `CoherentNatC0Stages` interfaces apply. Until then,
`prop:C0-free-generic` stays marked partial.

## Certification

Dedicated workflow `track-a-fair-functional-recursion.yml`
must compile the exact finite recursive data and check the
six endpoints in `CheckC0FunctionalFairRecursion.lean`,
with no placeholders or nonstandard logical assumptions.
The internal adversarial audit does not replace that check.
