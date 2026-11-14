# Track B: literal birth coordinates and sizes (12 November 2026)

The finite uniqueness argument must recover target request records from
images of complete old supports and entire fresh blocks. This note
records elementary but important exact identities in the actual birth
carrier. They are not statements up to isomorphism.

## Mathematical claims

For a request r at stage n, its old support is exactly
`r.support.image (toVertex F K n)`. Its fresh block is exactly
the image of all ordinals `Fin r.code.1.val` under
`i ↦ ⟨n, ⟨r,i⟩⟩`. Both maps are injective, giving cardinalities
`|P_r| = |r.support|` and `|B_r| = r.code.1.val`.
The support membership theorem records the literal preimage witness.

## Adversarial review: six independent mathematical checks

1. **Old naming:** `birthSupport` uses the successor-stage
   `toVertex(n+1)` on `Sum.inl`; this is definitionally the
   old `toVertex(n)`. The equality does not pick an abstract
   representative or move old support vertices to a new level.
2. **Fresh naming:** Each fresh vertex has exactly the original
   stage number n, the precise request record r, and one ordinal i.
   All ordinals of the local code are included, not just the root.
3. **No collisions:** Both cardinality equations use actual
   injective maps, `toVertex_injective` for old vertices and
   literal recovery of `i.val` for fresh vertices. Without
   injectivity, `Finset.card_image` could underestimate size.
4. **Support membership:** The reverse direction of membership
   is equality, not merely existence of some old vertex with an
   isomorphic local type. This is needed to interpret the image of
   a support under a partial source embedding.
5. **No assumptions on the growth class:** The statements are
   about the constructed tagged carrier. No claim of membership
   in the published growth class or of amalgamation is required.
6. **Scope of uniqueness:** These cardinality facts do not by
   themselves construct the ordered old-support isomorphism of
   an arbitrary finite embedding. They will be combined with
   complete support/block images, the order and the induced graph
   to derive the full request code. The remaining represented-level
   uniqueness induction and monoid identification stay open.

No manuscript validation marker is upgraded. Require exact-head
Lean compilation, standard axiom check and placeholder scan.

```sh
lake build BigHrushovski.CFBirthLiteralCoordinates
lake env lean CheckAxiomsCFTrackBLiteralCoordinates.lean
python3 scripts/check_no_placeholders.py
```

These are internal role-separated adversarial checks, not external
human referee reports.
