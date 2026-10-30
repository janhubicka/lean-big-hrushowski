# Adversarial audit: complete b-values in a selected C_F batch

30 October 2026

## Mathematical claim

For a selected request r and a complete selected old source S, the
auxiliary b-value of a fresh vertex is the entire literal old
support P_r together with every fresh vertex in r's block. Under
a simultaneous tagged map, its image is exactly the target
support Q_{T(r)} together with the whole tagged target block
if Q_{T(r)}=f[P_r] and the ordinal map is surjective.

This is a finite equality of *complete* set-valued function
values; it is not merely inclusion and not merely an assertion
about edges or neighbourhoods.

## Role-separated hostile checks

1. **Function-value referee.** b(v) contains all old support
   vertices and all new vertices of a block. A map that only
   preserves the block, the old-neighbour set or the support
   generators does not suffice. The source value is explicitly
   defined on the whole selected carrier and the target is the
   literal union of taggedSupport and taggedBlock.

2. **Finite-image referee.** Equality of the target block
   requires surjectivity of each finite ordinal map; an
   increasing proper injection would miss vertices. This
   property is available for actual transport by
   selectedGrowthOrdinalIso, but it is an explicit hypothesis
   of the generic theorem. The empty support causes no
   problem and introduces no phantom old vertices.

3. **Named-support referee.** The image of the old support
   must be equal to the full literal named target support.
   Merely requiring inclusion may give a smaller image than
   b(f(v)). The actual constructed target request supplies
   equality by transportGrowthStageRequest_support.

4. **Induction referee.** This establishes the values for
   *new* selected blocks at one level. Old vertices may have
   b-values involving earlier levels; their preservation is
   supplied by the finite-lifting induction hypothesis.
   The actual-map corollary uses the constructed target request
   and its canonical surjective ordinal isomorphism, with no
   separate support-equality or ordinal-surjectivity hypothesis.
   The corollary alone is not a complete functional embedding
   nor a proof of finite unique level lifting.

5. **Lean/kernel referee.** The exact endpoint is recorded
   in CheckAxioms.lean. Full compilation, standard axiom
   audit, placeholder scan and finite regressions are
   required before certification. There are no new axioms,
   unproven assumptions about the graph, or sorry statements.

These are distinct adversarial mathematical checks within the
project, not independent external human referee reports.

## Next bridge

The generic theorem is instantiated with selectedGrowthTag and
selectedGrowthOrdinalIso. The next step is comparing the induced map with
the actual birth-labelled vertices and prove that all
old vertices preserve their previously constructed complete
b-values. Combining this with the verified graph inducedness,
stage order and strict d-closedness will give a one-level
functional lifting step.
