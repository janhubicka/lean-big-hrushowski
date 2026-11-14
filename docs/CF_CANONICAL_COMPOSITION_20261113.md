# Track B: canonical finite prescribed lifts compose

13 November 2026. Stacked on PR #509, which handles arbitrary
genuinely partial finite ordered b-embeddings.

## Main statement

Let s be any finite b-closed source in the actual countable C_F
birth structure. Let e be its constructed prescribed lift for
level1, and let t=e[s] be its **literal** finite image. Let g be
the constructed prescribed lift of t for level2. Then

    g ∘ e = lift_s(level2 ∘ level1)

as functions on the literal source subtype. All three lifts may
use different finite stage covers. The target-level assignment
level2∘level1 is required to be strictly increasing only on the
finitely represented levels in s; the new theorem *derives* this
strictness from the completed composite, not as an extra input.

The intermediate image closure proof is
`finiteSourcePrescribedLift_image_bClosed`. Its result supplies
the explicit closure hypothesis of `finiteSourcePrescribedLift_comp`;
no external noncanonical image selection is necessary.

## Adversarial referee panel (internal roles)

1. **Stage-cover challenge.** The source, intermediate image,
   and final source lifts allow independent covers n1,n2,n3.
   Composition uses the actual birth carrier, not a selected
   whole-stage embedding.
2. **Image-closure challenge.** Full target b-value preservation
   forces the literal image to be b-closed. The result does not
   infer closure from graph inducedness or injectivity alone.
3. **Level gaps challenge.** The new general strictness lemma
   extracts monotonicity using the reflected birth-level preorder.
   It imposes no conditions at unused levels and permits the first
   represented target level to be zero.
4. **Order challenge.** The composite retains both canonical
   vertex order and birth-level preorder; preserving the latter
   alone would not identify fresh ordinals within a request.
5. **Uniqueness challenge.** The final equality invokes the
   arbitrary finite embedding uniqueness theorem via PR #509,
   not just uniqueness among maps built by a recursive template.
6. **Proof independence challenge.** The new theorem explicitly
   uses PR #509 and the prior finite uniqueness theorem; it does
   *not* prove a countable embedding monoid, a global R/H
   composition theorem, or Ellentuck's A.3/A.4. The stage-cover
   and closure hypotheses are spelled out rather than hidden
   in informal language.

These are six internal adversarial mathematical review roles,
not reports from independent human reviewers.

## CI requirements

```sh
lake build BigHrushovski.CFPrescribedFiniteLiftComposition
lake env lean CheckAxiomsCFTrackBCanonicalComposition.lean
python3 scripts/check_no_placeholders.py
```

Do not merge or promote manuscript validation markers until both
PR #509 and this stacked PR pass exact-head Lean/axiom/placeholder
verification. The still-open next task is an R/H-language
composition corollary and the coherent countable assembly.
