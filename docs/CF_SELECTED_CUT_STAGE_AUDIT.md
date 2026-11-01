# Track B: exact finite b-closed source cut and selected family

1 November 2026. Internal role-separated mathematical checks.

Theorems in `CFSelectedCutLevel.lean`:

- `selectedRequests_support_subset_stageCut`: for every selected
  request r met by a finite b-closed source, its **literal old
  support** is included in the actual preceding stage cut.
- `stageCut_succ_eq_selectedSourceImage`: the entire finite cut
  at the next level equals the image of one selected carrier
  consisting of that old cut and **every** ordinal of every
  selected request block. No copied, renamed or missing block.
- `selectedCut_growthTransport_of_induced_dClosed`: the whole
  next-cut request family has a valid actual partial-source
  transport certificate, assuming only an induced injection of
  the old source cut with strictly d-closed target old image.

## Hostile referee roles

1. **Literal image:** equality holds in the actual old/new
   successor-stage carrier, not up to graph isomorphism. This
   is necessary to iterate maps on true birth labels.
2. **Whole blocks:** b-closedness is crucial: without it a
   source cut could contain one vertex but omit another
   vertex of its selected block, and the image equality fails.
3. **Exact support:** source support inclusion comes from the
   b-closed predicate, not merely graph adjacency. It is a
   subset of the selected old stage cut, not of an unrelated
   abstract source carrier.
4. **Empty old cut:** at the first represented level the
   selected old set may be empty, even if the complete ambient
   source stage is nonempty. No `U_n→U_m` total map appears.
5. **Closure:** target support d-closedness is obtained from
   the already verified automatic strict closure theorem;
   the old image must still be strictly d-closed in the full
   target old stage. The theorem does not infer it from
   arbitrary inducedness.
6. **One simultaneous level:** there is no sequential
   attachment that would move different selected blocks to
   different target levels.
7. **Kernel:** three exact axiom endpoints are registered. A
   complete Lean build and axiom/placeholder/regression
   checks must pass before any new manuscript green marker.
8. **Remaining:** this identifies the source cut, constructs
   local transport certificates, but does not derive the
   full old-value induction, multi-level map, unique finite
   lift, or compatibility with restrictions and compositions.

These are internal checks and not independent human referees.
