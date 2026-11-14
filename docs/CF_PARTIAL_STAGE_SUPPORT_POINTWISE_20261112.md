# Track B: pointwise partial-stage support coordinates

12 November 2026. The previous `finiteStageSupportOrderIso`
provides a genuine order isomorphism between two named supports
from a map of a selected finite birth source. For uniqueness of
the ordered request code, it is necessary to know the precise
image of each individual support coordinate. This endpoint
extracts that identity from the witness used in its construction.

## Six-role adversarial audit

**Referee 1 — the same map:** The new equation uses the exact
input finite partial embedding e, not an arbitrary order
isomorphism chosen afterwards. The codomain coordinate is
chosen as a preimage of `e(toVertex n u)`.

**Referee 2 — exact target support:** The witness q belongs
to the *literal* finite subset Q of U_m because the image
e[P] is equal to Q's birth image. An inclusion in a larger
target stage would not identify the intended request support.

**Referee 3 — witness independence:** Target stage birth maps
are injective. Even though the existence proof chooses a
preimage classically, its image under `toVertex` is fixed
by the pointwise equation; no arbitrary renumbering remains.

**Referee 4 — empty cases:** For empty supports there is no u
to instantiate, so the statement and proof require no
inhabitant of U_0 or any source old stage. No global
extension of the partial embedding is made.

**Referee 5 — order and graph:** Canonical-order compatibility
is inherited through the existing construction of the
support order isomorphism. This lemma is only an identity
of vertex images, not a statement about adjacency or
complete ordered matrix codes.

**Referee 6 — formalization boundary:** The proof unfolds the
already verified order-isomorphism construction to recover
the chosen existential witness. It must be typechecked
together with the exact definition at the current head.
The next theorem must combine it with complete fresh
ordinals and inducedness to prove request-code equality.
No finite uniqueness or monoid theorem is claimed here.

This is an internal six-role audit rather than independent
human refereeing. No manuscript validation markers change.

```sh
lake build BigHrushovski.CFPartialStageSupportPointwise
lake env lean CheckAxiomsCFTrackBSupportPointwise.lean
python3 scripts/check_no_placeholders.py
```
