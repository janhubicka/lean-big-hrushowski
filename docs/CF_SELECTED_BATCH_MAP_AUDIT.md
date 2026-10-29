# Adversarial audit: simultaneous selected C_F level maps

29 October 2026

## New finite interfaces

The source carrier is the disjoint sum of the actual selected old
subtype S and all dependent fresh ordinal blocks indexed by the
selected literal request family D. This avoids choosing a sequential
order on the blocks and ensures every block is mapped into the
*same* target level.

- The source inclusion into its complete original tagged level is
  injective.
- Given an injective old map on S, an injective request-tag map and
  injective maps of the individual fresh ordinal intervals, the
  entire simultaneous map into the target tagged level is injective.
- The full induced-graph comparison follows from old-old,
  old-fresh and same-request fresh-fresh comparisons. Different
  request blocks have no edges in either actual tagged level.
- Independently, the target old image together with all selected
  fresh blocks is strictly d-closed in the complete next level
  whenever the old image is strictly d-closed and each selected
  request has support in it.

## Four hostile proof perspectives

1. **Dependent-type referee.** The fresh carrier is a dependent
   sum over the *selected literal requests*, not an undifferentiated
   finite ordinal. Distinct request tags must remain distinct after
   transport. The proof explicitly uses injectivity of the request
   map and injectivity of the within-tag ordinal maps. A map
   preserving only fresh sizes cannot give whole-batch injectivity.

2. **Graph referee.** Distinct fresh request blocks have no
   cross-edges in the actual source or target graph. The
   no-cross theorem is used in *both* directions, not merely to
   preserve positive edges. Source/target old-fresh and internal
   fresh-fresh adjacencies are explicitly required as equivalences.
   All nonedges are reflected.

3. **Predimension referee.** The closure theorem concerns the
   image in the *entire* target tagged level, not only the
   partial induced graph. It reuses the already certified
   supported-subbatch theorem, rather than trying to iterate
   one-block responses (which would shift subsequent target
   block levels). The old image must be strictly d-closed and
   all new supports lie inside it.

4. **Order/refinement referee.** A simultaneous map with an
   injective request tag function is not automatically
   order-preserving: the tag function must preserve the
   precise request lexicographic order and within-tag maps
   must preserve ordinal order. The already verified actual
   request transport theorem supplies the first condition;
   an exact ordinal equality/cast theorem is still needed.
   This result intentionally does not promote the full
   finite level-lifting lemma.

## Verification boundary

Compilation by the full Lean project, a standard-axiom audit,
the placeholder scan and configured finite regressions are
required before certification. The four exact endpoints are
registered in CheckAxioms.lean.

The current results are *conditional* finite-map and closure
interfaces. Deriving old-fresh and fresh-fresh graph
equivalences directly from the actual transported local
request codes, identifying the whole map image with the
selected target subbatch, proving the precise stage order
and b-closure, and inducting over represented levels
remain necessary.

These are role-separated adversarial checks conducted within
the project; no independent human referee panel was convened.
