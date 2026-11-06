# Track B: adversarial audit of a complete one-level functional map

1 November 2026 — internal checks, not independent human referees.

## Claim and exact hypotheses

A selected source carrier consists of the old subtype `S` and *all*
fresh blocks in a chosen family `D`. The actual old map is
`e : SupportCarrier U S → V`, with no extension to `U → V`.

A one-level map combines the already verified actual request
constructor, ordinal isomorphism, graph inducedness, exact stage order
and strict d-closed image. Newly, `selectedOneLevelBValue` and
`targetOneLevelBValue` define **complete auxiliary b-values on all
vertices**, including old ones. If old values lie entirely inside
`S` and the prescribed old map transports each onto the corresponding
target old value, then the actual simultaneous partial map transports
every one-level b-value onto the complete target value.

The endpoint `CFCoherentTower.selectedGrowthBatchMapSubtype_oneLevel`
packages (i) injectivity, (ii) preservation/reflection of edges AND
nonedges, (iii) the inherited strict order, (iv) strict d-closedness
in the **entire** target successor stage and (v) exact values of b on
**every** selected source vertex.

## Separate hostile mathematical checks

1. **Domain/empty-target referee:** the old map has domain only `S`;
   `U ≠ ∅`, `S=∅`, `V=∅` remains possible. No dummy value
   or entire old-stage embedding can be silently supplied.
2. **Value/reflection referee:** equality of full sets is proved, not
   merely inclusion or generator preservation. The source fresh value
   contains the full old support and **every** vertex in its fresh
   block. Old values are not constructed from thin air: a *separate
   explicit hypothesis* says they are transported onto target values.
3. **Closure referee:** strict d-closedness of `e[S]` in the full
   target old stage is a necessary premise for the full-image theorem;
   being order-preserving or graph-induced alone does not imply it.
   The selected request transport record also requires each named
   target support to be d-closed in its entire target old stage.
4. **Graph referee:** the claim uses the actual partial-source
   inducedness theorem, which covers cross-block nonedges and
   old-to-new nonedges. A graph homomorphism is not enough.
5. **Order referee:** the finite tower uses its genuine
   `stageLinearOrder`, not an arbitrary ranking. The target stage
   may be earlier than the source stage, with no level-gap condition.
6. **Representation referee:** the auxiliary `b`-values given
   here are parametric on old values. This does **not** yet instantiate
   the actual countable birth-block `b` operation nor the final
   `(R,H)`-presentation. That bridge and the induction over all
   represented levels must still be proved.
7. **Uniqueness referee:** the combined theorem produces one
   well-behaved map; it does not prove that every possible embedding
   with a prescribed level assignment is that map. The missing
   uniqueness step must derive complete target tag equality from
   the preserved literal supports, local graph codes and ordinals.
8. **Kernel/source referee:** two new exact `#print axioms`
   endpoints are registered. The branch must pass complete Lean CI
   (build, standard axiom audit, no placeholders, regressions).
   No manuscript green marker may be promoted before full CI.

## Remaining steps

Construct the actual selected old and target `b`-functions from
finite stages and show that the inductive `hOldB` hypothesis
matches their complete values. Derive the selected request family
`D` from each finite b-closed source cut. Prove the uniqueness
of the target request tag and ordered block using all code data.
Induct over represented source levels, including skipped levels,
then formalize compatibility of restrictions/compositions. Finally
identify the resulting finite lifts with `(R,H)` embeddings.
