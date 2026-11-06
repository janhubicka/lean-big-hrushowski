# Track A — adversarial audit: actual fair countable C₀ graph and unary limit

Date: 6 November 2026. Roles below are adversarial checks by the
assistant, not independent human or external referee agents.
Source modules: `C0FunctionalNatStageTransport.lean`,
`C0FunctionalNatStageCanonical.lean`,
`C0FunctionalFairLimit.lean`.
Stacked on the finite successor and recursion PRs #334 and #340.

## Main objective

Turn the **actual recursively chosen** finite stages into a coherent
countable graph on ℕ and one complete finite-valued unary operation.
The finite stages are on consecutive `Fin(size n)` carriers.
Each successor's old map fixes every numerical coordinate, preserves
both graph edges and nonedges, and transports its *complete canonical
unary values* by equality.

The construction then produces an actual `CoherentNatC0Stages`
using the previous verified coherent graph/unary interfaces.
It provides finite canonical certificates on every literal
Nat-stage carrier, strong finite covers in the graph limit, and
an explicit conditional recognition statement for the graph reduct.
No functional Fraïssé extension property is silently postulated
as a conclusion.

## Referee 1 — original numeric labels

The finite ordinal inclusion is the exact `Fin.val` map into ℕ.
Old successor maps are not arbitrary injections: their pointwise
numeric values are fixed, and the resulting graph agrees at each
old pair of actual Nat labels. The proof does not replace the old
carrier by an isomorphic but renumbered finite copy.

## Referee 2 — nonedges

The finite Nat graph is `GraphOn.transportedToNat`.
Inducedness is a biconditional. The successor's `old_graph`
field is likewise an iff, so an edge cannot appear later between
two previously nonadjacent vertices.
The existing `CoherentNatGraphStages.limitGraph_induced` theorem
then identifies the induced graph on every finite stage.
Failure to reflect nonedges would invalidate predimension,
self-sufficiency, and the component-dependency closure.

## Referee 3 — finite support of unary values

The complete unary value of `x < size n` is the image of its
canonical finite value in `Fin(size n)`; hence it lies in
`Finset.range (size n)`. Off that stage it is declared empty,
which is harmless because coherence is required only for vertices
already present. No one-generated closure becomes infinite
during the countable union.

## Referee 4 — exact old-value equality

The transported unary equality applies to the complete finite
Finset of **all** backward-reachable components of each old
vertex. It follows from the successor's `old_values` and
`old_labels` through image composition. Inclusion would not
suffice. The already proved coherent unary limit therefore
agrees with the finite value at any containing stage and makes
each stage a genuine functional substructure.

## Referee 5 — canonical finite index

For the literal carrier `Finset.range(size n)`, use the explicit
equivalence between `Fin(size n)` and its subtype of ℕ.
`FiniteC0.minimalSteps_relabel` and
`canonicalValue_relabel` transport the entire canonical
presentation. No externally chosen numbering of the finite
carrier is needed, and unused index ranks remain allowed.

## Referee 6 — strongness is derived

The previous `CoherentNatC0Stages.strong_steps` theorem
proves that complete unary closedness of each old finite
stage in the successor makes it strong there. The
`CoherentNatGraphStages.asStrongChain` theorem then gives
global strongness of all finite stages and finite strong covers
in the countable graph limit. Strongness is NOT inserted
as a new assumption about the countable structure.

## Referee 7 — actual versus abstract sequence

The graph and unary stage sequences both take their data from the
same `fairStages : ℕ → FiniteFunctionalNatStage` defined by
`Nat.rec`. The graph and unary carrier sizes are therefore
definitionally identical at every stage, not merely eventually
isomorphic. The exact finite certificates likewise come from
that same selected stage, not from an unrelated independent choice.

## Referee 8 — genuine remaining functional extension

Although the finite fair-step theorem answers each applicable
*catalogued* request, the construction still needs a separate
theorem showing that any finite functional extension
over an arbitrary stage can be encoded as a request in
`FunctionalC0RequestCatalogue`, with the original old
labels and canonical values preserved. Then fairness must be
combined with persistence of applicability to show that it
is eventually answered in the limit.

Only then can `HasCanonicalStageExtensionProperty`
be discharged in
`fairLimitReduct_generic_of_functionalExtension`.
Until that final request-coverage/encoding step has passed Lean,
the unconditional identification with `M₀` remains OPEN.

## CI and scope

The dedicated `track-a-nat-functional-stage.yml` workflow
builds `C0FunctionalFairLimit.lean` (and all its predecessors),
checks named theorem axioms, and runs the no-placeholder scan.
No manuscript countable green marker is justified before the
exact branch passes. The adversarial roles above are proof
review, not an independent kernel certificate.
