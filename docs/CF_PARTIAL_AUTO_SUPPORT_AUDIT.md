# Track B: adversarial audit of automatic named-support closure

1 November 2026.

## Statement

If `S` is the selected old-source subtype and
`e : SupportCarrier U S → V` is **injective and induced**,
with `e[S] ≤d V`, then any `P ⊆ S` satisfying
`P ≤d U` has literal target support `e[P] ≤d V`.
Consequently `SelectedGrowthTransportSubtype` is constructed
from the single old-map data and `r.support ⊆ S` for every
selected request. Individual per-request induced and target
d-closure assumptions are NOT needed.

The argument is:
`P ≤d U ⇒ P ≤d S` by restricting the endpoint;
`P ≤d S ⇒ e[P] ≤d e[S]` using exact induced predimension
invariance on the *selected subtype*;
`e[P] ≤d e[S] ≤d V` by transitivity.

## Adversarial referee roles

1. **Empty domain:** If U is nonempty, S and V empty, the
   proof never constructs U→V. The unique map from empty
   subtype is allowed, and P is then empty.
2. **Strict versus weak:** All three steps use `IsDClosed`,
   not merely `IsStrong`. A weak-closure substitution here
   would fail the actual target request constructor.
3. **Outside-source edges:** It would be wrong to transport
   `P ≤d U` immediately to `e[P] ≤d V` without showing
   `e[S] ≤d V`; this is an explicit premise.
4. **Inducedness:** Both edges and nonedges on S are reflected.
   A homomorphism need not preserve predimension, and no
   such weaker hypothesis appears in the theorem.
5. **Literal labels:** The intermediate support is
   `supportInside S P hPS`; its image under subtype inclusion
   is literally P and its image under e is literally the named
   target support. It is not an arbitrary isomorphic copy.
6. **Source request scope:** Every StageRequest provides
   `r.supportClosed` in the complete old source stage.
   The only new source hypothesis is `r.support ⊆ S`.
7. **Kernel:** Three exact axiom endpoints are registered.
   Complete Lean CI must pass before the statement is called
   machine-verified or promoted to a manuscript green marker.
8. **Remaining:** This constructs the selected transport
   record; it does not prove old-image closedness, old
   b-value preservation, selection of D, multi-level
   iteration, uniqueness or embedding monoid.

These are internal adversarial checks, not outside human referees.
