# Track B: target supports determined by the earlier map

12 November 2026. Two elementary, genuinely partial rigidity
facts needed in the uniqueness induction.

## Core statement

For a fixed source request r, the complete b-value and the
reflected level preorder recover the entire target block.
The target block is independent of which source fresh
ordinal was used. For two such finite maps e and g which
agree on all original vertices born before n, the whole
source old support P_r lies among those earlier vertices.
Hence e[P_r]=g[P_r]; full support-recovery identifies these
with the *literal named supports* of the respective target
requests, so those supports are exactly equal.

## Six adversarial referee roles

1. **Independence of chosen fresh ordinal.** Both witnesses
   use the same source request r and its complete source
   block, whose selected image is independent of i and j.
   Their targets need not yet have the same request tag.
2. **No partial block omission.** The exact b-value premise
   and the level-preorder equivalence yield a whole target
   block. A one-sided image inclusion would not justify
   equality of target blocks.
3. **Earlier support only.** Every vertex of the source
   named support is born strictly before n. The hypothesis
   e=g is applied only on these source vertices, not on
   all vertices of the old ambient stage U_n.
4. **Literal support equality.** The final equality concerns
   the precise finite vertex sets named by target request
   tags, not isomorphic copies or support sizes. No
   function on unrepresented source levels is introduced.
5. **Empty supports.** If the source support is empty the
   equality holds without selecting an old source vertex.
   This includes first represented levels mapping to
   target level zero.
6. **Scope and dependencies.** This is not yet target
   request-tag equality. It supplies the support hypothesis
   for `request_eq_of_support_size_adjacency`.
   Fresh size, complete ordered adjacency bits and a
   represented-level induction remain separate. No
   manuscript uniqueness marker is promoted.

## Verification gate

```sh
lake build BigHrushovski.CFArbitraryFiniteTargetSupportAgreement
lake env lean CheckAxiomsCFTrackBTargetSupportAgreement.lean
python3 scripts/check_no_placeholders.py
```

The six independent adversarial roles are internal checks,
not external human peer review.
