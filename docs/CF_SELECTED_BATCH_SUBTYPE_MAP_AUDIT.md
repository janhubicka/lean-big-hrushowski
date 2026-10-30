# Adversarial audit: simultaneous C_F batch map over a partial old domain

30 October 2026

## Corrected interface

The simultaneous selected-level map now takes the actual
old-source embedding
  e : {u : U // u ∈ S} → V,
rather than a total U→V. The selected source carrier already
contains this subtype, so its old branch is e itself. All new
blocks are represented by dependent pairs (r,i) with their
literal request tag and finite ordinal.

This remains well-typed if U is nonempty while S and V are
empty; no dummy target vertex or arbitrary totalization is used.

## Hostile mathematical checks

1. **Empty target.** If S=∅ and V=∅, the old map e is the
   unique empty function. The simultaneous map still sends
   any selected new blocks into actual target request blocks.
   A total U→V is never constructed.

2. **Injectivity.** Old-old equality is reflected by injectivity
   of e on its exact selected source. Old and fresh vertices
   live in opposite summands. Two fresh vertices with different
   selected tags cannot coincide when T is injective; for the
   same tag, injectivity of phi_r reflects their ordinals.
   Neither an arbitrary numbering of requests nor graph
   inducedness is assumed for this combinatorial assertion.

3. **Exact image.** Equality of the image with the old image
   together with the complete target blocks requires each
   ordinal map phi_r to be **surjective**. An injective proper
   map of a smaller ordinal interval into a larger one would
   leave target vertices outside the image.

4. **Predimension.** The old image e[S] must be strictly
   d-closed in the whole target old graph, and every target
   request support must be contained in this image. Under
   these explicit assumptions the previously verified
   supported-subbatch lemma proves d-closedness of the
   selected image in the *entire* target tagged level.

5. **Remaining functions and graph.** Injectivity, exact image
   and strict d-closedness do not establish inducedness,
   order preservation or complete block-support b-values.
   The previous total-map results supply useful proof
   patterns, but they cannot be substituted without a
   proof that a total extension exists.

6. **Lean.** Three exact endpoints are registered. Full
   compilation, standard axiom audit, placeholder scan
   and finite regressions on the same commit are required
   before promotion to Lean-verified status.

These are role-separated adversarial mathematical checks
within the project, not independent human referee reports.

## Next step

Instantiate T(r) with the genuinely partial request
transport from PR #255 (and its full code equality from
PR #256), using the exact image of each source support.
Use the canonical Fin cast to obtain bijective ordinal
maps. Then prove the graph boundary, inherited stage order
and complete b-values for the actual partial simultaneous
map. Only after induction through the represented levels
can the full finite unique lifting and embedding-monoid
theorems be certified.
