# Track B: exact b-value naturality under finite restriction

12 November 2026. This file is independent of the outstanding
finite uniqueness induction. It supplies the preparatory
finite-closed-source algebra needed to prove compatibility
of unique lifts under restriction.

## Statement

If s⊆t are finite b-closed sets in the actual countable C_F birth
carrier, the literal inclusion i:s→t carries the entire finite
source b-value computed in s onto the finite b-value computed in
t: i[b_s(x)] = b_t(i(x)). Any complete-b preserving partial map
e:t→M_F^† therefore restricts to a complete-b preserving
map e∘i:s→M_F^†. A target-level assignment strictly increasing
on levels represented by t remains strictly increasing on
those represented by s.

## Six adversarial referee roles

1. **Literal inclusion:** i does not identify or renumber birth
   vertices. It is a genuine injection of dependent source
   subtype carriers, and works even for empty s and/or t.
2. **Closedness is essential:** If s were not closed under its
   complete b-values, restricting e could omit old supports or
   fresh block vertices. Both s and t are explicitly assumed
   b-closed. The proof uses exact ambient b-values, not merely
   monotone inclusion of restricted sets.
3. **Whole-set equality:** The proof compares images under the
   injective forgetful map of the target subtype and then uses
   `Finset.image_injective` to recover equality of the
   *entire finite subsets*. No hidden cardinality-only
   argument or one-sided inclusion remains.
4. **No global extension:** The original map e is defined only
   on the larger finite source t and is evaluated only there.
   There is no assumption of an ambient embedding outside t.
5. **No unnecessary level assumptions:** Strict increase is
   required only on represented levels; representation in s
   implies representation in t by the exact inclusion
   of the source finite sets. Unused levels are unrestricted.
6. **Scope and verification:** This file does NOT prove
   restriction compatibility of canonical lifts by itself.
   For that, verify inducedness/injectivity/order/level
   after restriction, then use the still-developing finite
   uniqueness theorem to identify the restricted map.
   It is not the countable embedding monoid theorem.
   Only exact-head Lean, axiom and placeholder checks may
   justify a new validation marker. These are internal
   role-separated audits, not external human peer review.

## Mechanical check

```sh
lake build BigHrushovski.CFFiniteClosedSourceRestriction
lake env lean CheckAxiomsCFTrackBFiniteRestriction.lean
python3 scripts/check_no_placeholders.py
```
