# Adversarial audit: request order over a selected old source

29 October 2026

## Why this theorem is needed

The previous complete-key transport theorem assumes an order
embedding of the entire old finite carrier U. In the manuscript's
finite lifting induction only the selected b-closed old source
S ⊆ U is embedded. When the prescribed target level is earlier,
the entire U may be too large to embed into its target stage.
This is a genuine logical distinction, not a technical inconvenience.

The new theorem only assumes `StrictMonoOn f S`, with every
source request support contained in S. The values of f outside S
are completely unrestricted. The target key's increasing support
tuple, fresh size and full adjacency matrix remain explicit
transport certificates.

## Role-separated hostile checks

1. **Order comparison.** The list-lex theorem must preserve and
   reflect proper-prefix comparisons and different support lengths.
   Its proof uses strict monotonicity only on elements actually
   appearing in the two lists. Arbitrary behaviour outside S
   cannot affect the result.
2. **Equality and collisions.** Equal mapped tuples must reflect
   equal original tuples on S. This follows from strict list-order
   transport and trichotomy; no global injectivity is used.
   The complete graph-code injectivity theorem then gives
   uniqueness of target requests and noncollision of distinct
   source requests.
3. **Finite lifting applicability.** An actual partial embedding
   e : S → V can be extended to a total map U → V when V is
   inhabited, without imposing order conditions outside S.
   If S and V are both empty, that base case must be handled
   separately. No embedding of the whole U into V is assumed.
4. **Predimension and admissibility.** The theorem does not
   manufacture a target local type. It remains necessary to
   prove the transported named support d-closed, the local
   graph C_F-admissible, its fresh size within the published
   bound, and the equality of its complete ordered code.
5. **Same-level assembly.** Once requests are transported,
   all selected blocks at a represented source level must
   map into the same target level simultaneously. The existing
   selected-subbatch d-closedness theorem supplies the
   closure part, but the induced map and order must still
   be assembled.
6. **Lean kernel.** Six exact theorem endpoints are registered.
   Full build, standard axiom audit, placeholder scan and
   finite regressions are required before certification.

These are adversarial mathematical checks within the project,
not reports by separately appointed human referees.

## Remaining gap

The total-map version here removes the whole-stage order
embedding requirement, but still assumes exact transported
support tuples and adjacency codes. Constructing these from
the actual partial old embedding and local graph relabelling
is the next proof step. Finite unique level lifting and the
countable embedding monoid remain unverified.
