# Adversarial validation of the coherent graph–unary C₀ limit bridge

Date: 1 November 2026. The seven referee roles are separate
mathematical checks by the assistant. They are not independent
human or external-agent referee reports.

## Hypotheses and result

`CoherentNatC0Stages` packages a coherent countable
graph-stage sequence and a coherent finite-valued unary
sequence with **identical** finite initial-segment carriers,
each stage carrying a minimal-component canonical C₀
presentation. The finite-stage unary function must agree
with the *complete* canonical unary values of the induced
finite graph on that literal carrier.

From this data the new proof derives the old stage strong
in each successor, the exact finite canonical certificates
for the limit graph and unary operation, and finite globally
strong covers. It then identifies the graph limit with M₀
under the **explicitly additional functional stage-extension
property**. The latter is NOT established by these stage
coherence statements alone.

## Referee 1 — complete function values

Coherence is exact equality of each old unary Finset, not
forward inclusion. The complete canonical unary value in
the successor sees all backward-reachable entire components.
The old finite carrier is therefore genuinely closed in
the successor. A proof using only back-neighbour sets or
the predecessor of a selected generator would be invalid.

## Referee 2 — strongness is derived

The proof does not assume strong graph successor steps.
The old stage is closed under the successor's full unary
operation; by the finite canonical-value strongness
theorem on the successor's entire finite carrier it is
strong there. This matches the paper's functional
self-sufficiency argument and avoids duplicating the
predimension/local-free-amalgamation calculations.

## Referee 3 — nonedges and induced copies

The countable graph is the union of graph stages preserving
both adjacency and nonadjacency. On every finite stage,
its induced graph is *equal* to the graph induced from
the finite stage graph. The auxiliary
`GraphOn.eq_of_adj_iff` uses function extensionality
and proof irrelevance to promote the biconditional
on every pair into equality of graph structures.
Without reflection of nonedges, predimension and
canonical dependencies could change in the limit.

## Referee 4 — no confusion of finite carriers

The canonical finite index lives on the literal subtype
`{v : ℕ // v ∈ stage n}`. Its graph is the induced
pullback along the subtype value map. The proof transfers
this exact graph across the induced equality, rather
than choosing an arbitrary finite relabelling which
may permute base labels or component chronology.

## Referee 5 — cofinality and no gaps

The common finite stage carrier is
`Finset.range (unary.size n)`, and sizes strictly
increase. Every finite set is contained in some
stage. The existing `NatStageCoverage` and the new
coherent unary finite-cover lemma discharge coverage
without an independent graph-finiteness assumption.

## Referee 6 — global strongness

Once old finite graph stages are strong in their
successors, `CoherentNatGraphStages.asStrongChain`
and `finiteStrongCover_of_strong_steps` establish
global strongness in the actual limit graph. This
does not depend on any countable automorphism or
genericity theorem and does not smuggle in an
unverified finite self-sufficient hull assumption.

## Referee 7 — remaining existence and extension

The source structure is conditional on *coherent
finite canonical stages*. It does not construct
those stages or prove they answer every
scheduled functional embedding request. Even
with canonical stages and strong covers, a
countable limit need not be the generic
without the functional extension property.
The endpoint
`limit_reduct_iso_generic_of_functionalExtension`
therefore retains that property explicitly.

The still-open construction step must combine
the strictly growing finite labelled responses,
the fair functional request catalogue, and the
graph and unary stage coherence. Only after
this construction and a fair-response theorem
can the countable `prop:C0-free-generic` be
marked fully validated.

## Certification gate

The dedicated workflow
`coherent-c0-stages.yml` builds the exact
module, checks eight named theorem-axiom endpoints
in `CheckCoherentC0Stages.lean`, and runs the
no-placeholder scan. No manuscript statement
should be promoted before the exact branch
source passes these checks.
