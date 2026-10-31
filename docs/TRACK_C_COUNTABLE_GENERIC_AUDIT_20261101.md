# Track C: countable C_F genericity certificate (1 November 2026)

Base: Lean main `1f5fcd06fe6fcdbfdfeab997125b31609df98b38`.
Manuscript: `The-big-Hrushovski`, v52, `sections/03b_enumeration_CF.tex`,
Lemma `lem:CF-finite-level` (especially the final paragraph of its proof).
This branch owns only `CFRealGenericCertificate.lean`, its isolated audit
entrypoint/workflow, and this note. Track B's partial-source level lifting is
**not** imported or required.

## Formal endpoint

`realCountableGraph_genericCertificate` combines three independently
validated facts about the **actual** birth-labelled countable graph:

1. The growth inequality `F(|S|) ≤ δ(S)` holds for **every** finite
   subset S, conditional on the initial stage's class membership and the
   stage-local strict d-closed free-amalgamation property.
2. For **every** finite subset S, a finite stage image contains S and is
   globally strictly d-closed in the entire countable graph.
3. For every finite growth-class graph H and finite inclusion
   `a ≤_d b`, any prescribed **induced**, injective embedding of a into
   the countable graph with globally strictly d-closed image extends to
   an induced embedding of b whose image is also globally strictly
   d-closed; old vertices are fixed literally. All target nonedges
   are preserved and reflected.

No new axiom, finite-size bound, request enumeration, or fair schedule
is imposed. The third fact invokes the merged theorem
`CFRealFiniteGenericity.finiteRealDClosedInterval_globalResponse`;
the first two invoke `CFCountableGrowth.countableGraph_growth_of_freeJoins`
and `CFCountableDClosedChain.stageImage_global_dClosed`.

### Exact remaining assumptions and obligations

- **Free amalgamation**: currently the theorem asks for the instance
  `∀ n, (stage (n+1)).graph.GrowthClosedUnderDClosedFreeJoins F_nat`.
  The paper assumes this property on the entire finite C_F class.
  The stage-local premise must be explicitly derived from the class-level
  one; neither follows merely from analytic monotonicity/unboundedness.
- **Initial graph**: the empty-stage growth premise is explicit. It is
  elementary from F(0)=0, but is not yet eliminated by this theorem.
- **Real domain**: Lean uses `F : ℝ → ℝ`. The printed paper takes
  `F : ℝ≥0 → ℝ≥0`. An explicit, monotone, unbounded extension/restriction
  adapter must be checked; negative arguments cannot be silently supplied.
- **Infinitude**: the certificate states finite stage coverage, not that
  the birth carrier is infinite. To identify it with the Fraisse limit,
  certify the one-vertex empty-support request at every level. The paper
  assumes the singleton belongs to C_F and ∅ is d-closed in every member.
- **Uniqueness**: no Lean theorem yet asserts that any two countable graphs
  with finite globally d-closed covers and all finite C_F extension
  responses are isomorphic. This requires genuine strict-d-closed
  back-and-forth, not the weak-strong back-and-forth already formalized
  for C_0. The object `M_F` is not defined by this certificate.

## Adversarial role-separated review (internal, not external referees)

- **Hypothesis referee**: checks that the class-level free-amalgamation
  condition and empty/singleton premises are not identified with
  F(0)=0, monotonicity, or unboundedness alone. The theorem retains
  hEmpty and hFree; the published-domain adapter remains TODO.
- **Closure referee**: checks **strict** global d-closedness of the
  container, not weak strongness, and checks closure is tested
  against every finite proper extension in the countable graph.
- **Embedding referee**: checks that the target copy preserves both
  edges and nonedges and that old vertices are fixed pointwise;
  no total map of a larger source stage is assumed.
- **Countable referee**: checks the finite response theorem is invoked
  on arbitrary labelled finite source and target, but that it does
  not by itself supply countable back-and-forth/uniqueness.
- **Certification referee**: verifies that the new endpoint is imported
  by an isolated build target, audited with `#print axioms`, and not
  promoted to the main statement registry or a manuscript green marker
  before passing CI.

### Test scenarios

- Empty finite prescribed source and target: the old map is unique and
  requires no total embedding of an unrelated old stage.
- Nonempty proper strong source: do not replace strict d-closedness by
  weak strongness.
- A target graph with a nonedge: the induced embedding must **reflect**
  nonedges, not merely preserve positive adjacency.
- A graph outside C_F: the extension theorem deliberately does not
  apply; the source-growth premise is substantive.
- A hypothetical bounded/nonmonotone F: cannot invoke the canonical
  numerical inverse. The real growth hypotheses are indispensable.

Status at branch creation: **new aggregate Lean theorem, CI pending**.
The manuscript's identification with M_F remains **PARTIAL** until
the exact published-assumption adapter, infinitude, and countable
uniqueness theorem are certified.
