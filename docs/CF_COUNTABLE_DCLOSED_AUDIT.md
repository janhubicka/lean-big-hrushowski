# Adversarial audit: globally strict d-closed finite stages in the countable C_F graph

16 October 2026

## Mathematical statement

The exact finite batch theorem certifies U_n <=d U_(n+1)
inside the successor finite graph. The countable birth graph
contains U_(n+1) as an induced subgraph (PR #159).
Transporting the finite strict d-closed inclusion through
the actual birth map therefore yields

    StageImage(n) <=d StageImage(n+1)

inside *the same fixed countable graph*.

The images of finite stages cover every countable birth vertex
(PR #156); hence they form the already certified strict
DClosedChain. Its stage_global lemma implies

    StageImage(n) <=d V

with strictness tested on all finite proper supersets
inside the countable graph.

## Five hostile proof reviews

1. **Whole-old-image referee.** The image of U_n inside
   U_(n+1), then under the birth-labelled map, must be
   *equal* to StageImage(n), not merely isomorphic.
   The equality uses the definitional old-map compatibility
   of toVertex and Finset.image_image.

2. **Inducedness referee.** The finite-stage d-closedness
   transfers to the countable graph only because PR #159
   proves the entire stage graph is induced: it preserves
   predimension of all intermediate finite vertex sets,
   including nonedges. A forward graph map is insufficient.

3. **Strictness referee.** The theorem uses IsDClosed,
   not IsStrong. The inherited strict inequality for
   every proper intermediate finite set is necessary
   to invoke the earlier stage_global lemma.

4. **Coverage referee.** Merely having a chain of
   d-closed inclusions could leave new ambient vertices
   outside their union, invalidating global strictness.
   The birth-labelled carrier is defined as the union
   of fresh layers and every vertex has a canonical
   finite-stage representative. The DClosedChain
   includes this coverage as a proof field.

5. **Scope referee.** This proves global strict
   d-closedness of finite stages but does *not*
   establish C_F membership for an arbitrary F
   (restricted free-amalgamation is still necessary),
   completeness of the local size bound K, or
   the full finite-extension property of the
   countable graph. In particular no functional
   R/H block-root theorem follows.

The result should receive a GREEN validation marker
only after the exact Lean theorem compiles with a
standard-axiom audit and no proof placeholders on
its final commit. The five roles are deliberately
separated internal mathematical checks; no external
independent referee agents were spawned.
