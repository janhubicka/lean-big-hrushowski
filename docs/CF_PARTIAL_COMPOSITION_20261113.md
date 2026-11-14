# Track B — composition of genuinely partial finite C_F embeddings

13 November 2026. Follows the merged finite-image b-value naturality
(PR #502), finite arbitrary-map uniqueness (PR #481), and finite
prescribed-level exists-unique theorem (PR #490).

## Mathematical statements

1. If e is an injective induced finite-source embedding preserving
   complete b-values, birth-level preorder, and canonical birth order,
   and g is such an embedding **defined only on the literal finite image
   e[s]**, then g∘e preserves and reflects all the same relations and
   preserves all complete b-values.
2. If the composite realizes a target-level assignment strictly
   increasing only on the levels represented in s, then it is literally
   equal to the constructed finite prescribed lift, regardless of the
   stage cover used for that construction.

The first theorem does not assume the finite source is closed separately:
its complete-b preservation hypothesis implies that its image is closed.
The second uses finite source b-closure to invoke the already verified
arbitrary-map uniqueness theorem.

## Six adversarial referee checks

- **Functional-value referee.** The whole auxiliary b-value, not just
  named roots or inclusion of supports, is transported; equality of
  finite b-values uses the existing exact finite-image naturality.
- **Partial-map referee.** The codomain of the first map is restricted
  to its literal finite image before the second map is applied. No
  total extension over a source stage or the countable universe exists.
- **Graph referee.** Both maps have biconditional adjacency hypotheses;
  composing these biconditionals preserves nonedges as well as edges.
- **Order referee.** Both the birth-level preorder and the actual
  canonical birth order are explicitly preserved and reflected by
  the composite. These assumptions cannot be dropped just from b-values.
- **Uniqueness referee.** The second theorem compares an arbitrary
  composite with the independently constructed finite prescribed lift
  via the arbitrary-map uniqueness theorem. It does not silently treat
  e or g as canonical or assume uniqueness of recursive choices.
- **Boundary referee.** Empty sources and skipped represented levels
  remain included. No global increasing map on ℕ, countable embedding
  monoid, or R/H composition theorem is claimed here. The hypothesis
  of a prescribed composite level assignment is explicit.

This is an *internal* six-role adversarial mathematical audit, not six
external human referee reports. The new declarations may be marked
Lean-verified only after exact-head kernel compilation, standard-axiom
checking, and the placeholder scan.

## Remaining work

Derive the strictly increasing represented-level assignment of an
actual composite automatically from the two finite prescribed lifts.
Then state the concrete canonical-lift composition identity, transport
it to the partial R/H language, and connect coherent finite maps to
the countable embedding space. Do not promote TeX validation markers
on the basis of an unverified branch.

## Gates

```sh
lake build BigHrushovski.CFPartialOrderedBComposition
lake env lean CheckAxiomsCFTrackBPartialComposition.lean
python3 scripts/check_no_placeholders.py
```
