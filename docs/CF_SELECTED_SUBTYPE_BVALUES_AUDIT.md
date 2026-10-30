# Adversarial audit: complete C_F b-values under a partial old map

30 October 2026

## Claim

For a selected fresh vertex of a request r, its complete
set-valued unary b-value consists of every vertex of the
literal old support P_r together with every fresh vertex
of the entire request block B_r. Under a simultaneous map
whose old component is only e:S→V, the image of this complete
value equals the complete target value, provided the target
support is exactly e[P_r] and the fresh ordinal map is onto.

For the actual target request and its canonical Fin order
isomorphism, both conditions are already proved, so this
is an unconditional one-level complete b-value equality
under the explicit selected old-source transport assumptions.

## Hostile mathematical checks

1. **Empty target:** If the selected old source and target
   old carrier are empty, the old value component is
   empty and no total U→V map or dummy target vertex
   is needed. Fresh blocks and their internal order
   remain valid.

2. **Full value equality:** Both directions are proved.
   Old support vertices are mapped *onto* the entire
   literal named target support. Fresh ordinals map
   onto the complete target block by the canonical
   Fin order isomorphism. Preservation of only the
   positive edges or only a generating support
   would not imply this set equality.

3. **Induction:** The theorem concerns new vertices
   at one selected represented level. Values of old
   vertices lie in earlier levels and must be
   transported by the induction hypothesis.
   This theorem alone does not prove a complete
   functional embedding or the finite unique lift.

4. **Dependency:** The new result does not assume
   noncollision of tags, inducedness of the graph,
   or preservation of the stage order. Those
   properties are separate inputs for full lifting.
   In particular the verified total-map b-value
   theorem is not used as a substitute.

5. **Lean/kernel:** Two exact axiom endpoints are
   registered. Full compilation, standard axiom
   audit, placeholder scan and finite regression
   checks are required before marking the
   result verified.

These are separate internal adversarial checks,
not reports by independent external human referees.
