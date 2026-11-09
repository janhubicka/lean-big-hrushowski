# Adversarial audit: unconditional countable C₀ functional genericity

Date: 8 November 2026. Target:
`BigHrushovski/C0FunctionalFairGeneric.lean`.

**Status:** proof proposed; not certified until the exact dependency
graph and this new module compile and the registered axiom audit
passes. The roles below are adversarial mathematical checks performed
within this review, not independent human referee reports.

## Statement and logical dependencies

The goal is the actual recursively constructed countable functional
structure from `C0FunctionalFairRecursion`, with the coherent graph
and full finite-valued unary limit from `C0FunctionalFairLimit`.
This is NOT a countable structure postulated to have the extension
property.

The required result is
`fairLimit_hasFunctionalStageExtension`, exactly
`FiniteC0.HasCanonicalStageExtensionProperty` for this limit.
The last theorem `fairLimitReduct_isomorphic_M0` then follows
from the already audited conditional reduct recognition theorem.

The proof has five main interfaces:

1. Exact canonical presentations on literal finite Nat stages:
   `fairLimitCanonicalStages`.
2. Exact stability and inducedness of both graph and complete
   one-generated unary values in the countable limit.
3. `exists_catalogue_diagram_of_functional_extension`: normalize
   a finite functional extension on arbitrary carrier `W` to
   an exact finite ordinal diagram with unchanged source labels.
4. `eventually_answered_in_fair_limit`: a catalogue request
   applicable at a finite stage is realized in the countable
   limit, with a complete-functional induced embedding
   fixing the original source labels.
5. The final proof transports the ordinal target back to
   the original carrier and discharges every literal field of
   `HasCanonicalStageExtensionProperty`.

## Referee A — a second index on the same finite source

The extension property's source witness
`κOld : {x // x∈stage n}→Fin p` need not equal the index
selected for stage n by the recursive construction. No numerical
reindexing theorem is assumed to make them agree.

Instead, the extension property's `hOldValues` identifies every
complete unary value under `κOld` with the *actual* countable
limit operation. The selected stage's complete unary operation
is identified with the same limit operation by exact coherence.
These equalities imply equality of the two complete unary
values as finite subsets of the **same** literal Nat stage.

The proof reflects equality through the injective
`Subtype.val` image map. It does not equate the component
indices themselves.

## Referee B — source versus target labelling

Let the finite stage's carrier be `Fin n` and let the
extension's source be the literal subtype of `range n`.
The equivalence `e : Fin n ≃ {x // x∈range n}` is the
numeric `finRangeEquiv`, not a chosen `Fintype.equivFin`.
The source-to-target finite map is `f∘e`.

The arbitrary target `W` may be relabelled to
`Fin(card W)` because it has no prior numeric labels.
The catalogue diagram's source remains **exactly**
the recursive stage model, and the catalogue request's
old label map is `x↦x.val`.

## Referee C — actual induced graph embedding

Both graph equalities (source to finite target and
finite target to the limit) are biconditionals on
adjacency. Nonedges are reflected. This is essential:
a one-way graph homomorphism would not preserve the
predimension, the minimal component dependencies or the
Fraïssé age.

The source graph equality uses
`fairGraphStages.limitGraph_induced` and
`natGraph_induced` on the literal numerical stage
before invoking the arbitrary-target normalizer.

## Referee D — complete unary images, not just support

The target `W` has a complete canonical value
`canonicalValue K κ x`. The target normalizer gives
its **entire** image along the finite equivalence.
The eventual finite response gives its full image
inside the countable limit, and composition yields
`C(gx)=(canonicalValue K κ x).image g`.
No fresh vertex can be introduced into an old unary
value after its finite stage, by exact unary coherence.

A proof giving only inclusion in one direction is
insufficient and must be rejected.

## Referee E — pointwise old agreement

The eventual response fixes each catalogue source label.
The embedding of the original carrier `W` is the
finite normalized target embedding composed with the
normalizing equivalence. For any original old point u,
the final map satisfies **literal**
`g(fu)=u.val`, not agreement up to an automorphism.
The proof uses the source equivalence identity
`e(e.symm u)=u` and equality of the normalized
diagram embedding.

## Referee F — no hidden countable homogeneity assumption

The proof of each finite successor uses only the
previously certified finite functional amalgamation and
forced growth. The choice of successors is explicit,
and the schedule revisits every encoded finite request.
`HasCanonicalStageExtensionProperty` is a **conclusion**
of `fairLimit_hasFunctionalStageExtension`, not a
hypothesis of any of the finite successor, recursion,
persistence or limit coherence modules.

The final isomorphism theorem invokes the pre-existing
strong generic uniqueness result only **after** the
functional extension property has been constructed.

## Referee G — nested structures and finite generation

A finite induced stage must have exact complete unary
values with no elements outside its carrier.
The new `CoherentNatUnaryStages` lemma establishes this
from finite support and stability, and the
`CoherentNatC0Stages` module derives finite globally
strong covers. The proof does not substitute an
arbitrary graph-strong substructure for a functionally
closed finite source.

## Referee H — finite cardinalities and empty source

The source stage may have `n=0`; in that case
`finRangeEquiv 0` and the empty source map are
well-defined and every old-value statement is
vacuous. The finite response theorem forces strict
growth regardless of whether a decoded request is
inapplicable, already realized or empty. This
prevents a countable sequence with bounded numeric
support and supplies real coverage of ℕ.

The target's chosen finite equivalence may permute
new vertices, which is harmless provided it
retains the prescribed source map as an explicit
composite; no assumption of equality of the
two component-order chronologies is imposed.

## Referee I — the final audit gate

Require all of:

- Exact kernel build of `C0FunctionalFairGeneric.lean`
  including the dependent fair-limit and finite
  request-normalization modules.
- `#print axioms` for all three new endpoints,
  allowing only the standard logical axioms
  `propext`, `Classical.choice` and `Quot.sound`.
- No `sorry`, `admit`, added axioms or
  `unsafe` declarations in the project sources.
- Existing exhaustive finite functional-value
  and stage-response regressions.
- Exact correspondence of the complete Lean theorem
  to the manuscript's (C_0) countable reduct step,
  with no extra hypothesis in the mathematical prose.
- Merge only after all required CI checks pass
  on the precise revision being merged. The
  manuscript countable marker stays partial until then.

A CI failure at an imported module must first be
isolated to that module; a conditional success for
the final theorem on a stale dependency is not enough.
