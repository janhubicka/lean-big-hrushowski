# Adversarial audit: simultaneous C_F inducedness with a partial old map

30 October 2026

## Exact theorem scope

An old map e : {u:U // u∈S}→V may have an empty codomain even when
the full source old carrier U is nonempty. The selected-batch
carrier is the disjoint sum of S and all fresh vertices of chosen
literal request tags, so its simultaneous target map is defined
without extending e to U→V.

The theorem proves preservation AND reflection of the complete
graph relation on all pairs of selected vertices, under explicit
induced old-old, old-fresh boundary and same-block fresh-fresh
equivalences and an injective map on request tags.

## Role-separated hostile checks

1. **Empty-target:** The old map e is only evaluated on selected
   old vertices. If S=V=∅, the source may still have selected
   fresh blocks. The theorem introduces no dummy vertex and no
   total map U→V.

2. **Graph:** Four pair types are checked: old/old, old/fresh,
   fresh/old (by graph symmetry), and fresh/fresh. The latter
   splits same-request local adjacency from distinct-request
   nonadjacency. The no-cross theorem applies to the actual
   tagged batch on both source and target, so nonedges are
   reflected and not merely preserved.

3. **Request identity:** Distinct source request tags must remain
   distinct in the target. The result explicitly assumes T
   injective; this is now available for the actual transported
   requests from merged PR #259, but the generic theorem does
   not silently take it for granted.

4. **Local graph bridge:** The old/fresh and same-block fresh
   equivalences are separate hypotheses. They must be discharged
   from the actual target request's named-base pullback and the
   literal support image under e. The current theorem does not
   itself identify the constructed target request or prove
   its b-value equality.

5. **Kernel/scope:** The exact axiom endpoint is registered.
   Full build, standard axiom audit, placeholder scan and
   finite regressions are required before marking the theorem
   verified. The finite unique level-lifting and embedding
   monoid statements remain unverified.

These are separate mathematical adversarial checks within
the project, not external independent referee reports.
