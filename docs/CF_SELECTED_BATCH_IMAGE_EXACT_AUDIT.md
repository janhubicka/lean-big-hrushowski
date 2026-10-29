# Adversarial audit: exact image of a simultaneous selected batch

29 October 2026

## Statement

The map sends the old finite selected source S by f and maps every
fresh pair (r,i) to the corresponding target request tag T(r) and
ordinal phi_r(i). If each phi_r is *surjective*, the image is exactly
f[S] together with every complete target block whose tag is in T[D].
No other vertices occur in the image.

If the old image f[S] is strictly d-closed in the target old graph
and every target request support lies inside f[S], the entire
image is strictly d-closed in the *whole* target simultaneous level.

## Role-separated hostile checks

1. **Finite coverage.** An injective fresh ordinal map alone is
   insufficient: Fin 1 can embed strictly into Fin 2 while missing
   the last vertex. Full image equality requires surjectivity
   of each phi_r. This hypothesis is not silently derived from
   request tag injectivity.

2. **Literal tags.** The image family is the literal image of
   the finite set of selected request records. All target
   blocks appear with their actual dependency-type tags and
   exact fresh ordinals. The map cannot create vertices of
   unselected target requests.

3. **Predimension.** The d-closedness result concerns the
   complete target level, not merely the selected induced
   graph. It reuses the previously verified supported
   subbatch theorem, which attaches all selected blocks in
   one level and does not assume that their order can be
   chosen successively.

4. **Empty cases.** Empty selected old source or empty family
   of requests does not imply a phantom fresh vertex.
   Image equality is valid for the empty batch. The target
   old-stage image is required to be d-closed, as stated.

5. **Relation/ordering.** Complete image equality and
   d-closedness are not yet assertions of inducedness or
   preservation of the manuscript's canonical order.
   The previous conditional selected map theorem supplies
   the inducedness criterion. It remains necessary to
   discharge its old-fresh and fresh-fresh graph equalities
   and to instantiate the tag and ordinal maps with the
   actual constructed request transport.

6. **Lean.** Three exact endpoints are registered. Full
   compilation, standard axiom audit, placeholder scan
   and finite regressions must pass before certification.

These are separate adversarial mathematical checks within
the project, not reports from external human referees.

## Next construction

Instantiate T(r) with transportGrowthStageRequest and phi with
the canonical cast between equal finite ordinal intervals.
Prove injectivity and surjectivity of phi, as well as the
target request support inclusion. The complete graph-code
transport gives local inducedness. This will supply a
strictly d-closed induced map at one target level, after
which order and b-value compatibility still require proof.
