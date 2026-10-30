# Adversarial audit: actual C_F batch over a partial old map

30 October 2026

## Exact construction

The selected old map is e : {u : U // u ∈ S} → V. Each selected
source request is transported to an actual target StageRequest using
the genuinely partial construction, and each fresh interval is mapped
by the canonical increasing Fin cast. All selected blocks are
transported into the same target tagged level in one step.

The target support is literally the image of its old source support.
Its inclusion in the old image is proved directly from the finset
images; no extension of e to all of U is assumed.

## Hostile mathematical checks

1. **Empty-target referee.** S=∅, V=∅ and U≠∅ are legal. The map
   e is the unique empty-subtype function and is never totalized to
   U→V. Every selected source support P lies inside S and is
   therefore also empty, so the target support image is empty.
   The module assumes only the actual target request's existence
   conditions, including strict closure.

2. **Dependent request referee.** Request tags remain dependent
   records over literal old supports. The fresh interval map is
   Fin.castOrderIso from the verified equality of fresh sizes,
   not an arbitrary injection. Surjectivity guarantees every
   vertex in a selected target block belongs to the map image.

3. **Predimension referee.** The full old image e[S] is required
   to be strictly d-closed in the target old stage. Every
   transported request support is proved contained in e[S].
   The previously certified selected-subbatch theorem then
   proves strict d-closedness of the complete image in the
   WHOLE tagged target stage.

4. **Graph/order referee.** The local old graph is assumed
   induced on each source support. This module does not claim
   inducedness of the entire selected batch or preservation
   of the precise stage order. The actual tag map's
   injectivity likewise remains separate; it will require
   reflection of equality of complete transported request
   codes under the partial old embedding.

5. **Lean/kernel referee.** Four exact axiom endpoints were
   registered. The entire import graph, standard axiom audit,
   placeholder scan and finite regressions must pass on one
   commit before the assertions may be marked verified.

## Remaining bridge

Prove the partial-map request-tag injection and exact
lexicographic order comparison, then apply the partial
simultaneous map's injectivity and the generic inducedness
criterion using the full local named-base graph. Transfer
complete b-values and extend the construction inductively
through represented levels.

These are role-separated adversarial mathematical checks within
the project, not independent human referee reports.
