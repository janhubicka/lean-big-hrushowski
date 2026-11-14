# Finite partial support order isomorphism — Track B, 12 November 2026

This small general lemma is shared by the finite C_0 component
calculus and the C_F request support calculus.

## Six adversarial referee roles

1. **Empty targets:** The source map is defined only on
   `{u : U // u∈P}`, not on all U. It still makes sense when
   the target ambient finite stage has no vertices. If Q=∅
   and the source support is empty, the unique empty map is
   sufficient; no target default value is chosen.
2. **Exact image:** Surjectivity of the support order map
   requires equality of its image with Q, not merely inclusion.
   Both directions are used: construction of a map into Q and
   recovery of each target-support vertex.
3. **Strict increase:** Strict monotonicity on the source
   support gives injectivity and order reflection through
   the finite linear orders. Merely induced graph equality
   or a map of unordered supports would not suffice.
4. **No hidden global map:** Neither definition nor proof
   evaluates e outside the source subtype. This is important
   for the first represented source level with empty old
   support and target stage U_0.
5. **Finite size:** The equality of support cardinalities
   is obtained from the actual order equivalence of the
   two subtypes. No relation to abstract isomorphism types
   or arbitrary renumbering is introduced.
6. **Proof scope and reuse:** There are no graph, predimension
   or C_F-class premises. Applying the lemma to birth-block
   supports will still require constructing the genuine
   partial old-stage map, its exact image and the order
   hypothesis. No finite unique level lifting is inferred.

## Exact-head verification

```sh
lake build BigHrushovski.FinitePartialSupportOrderIso
lake env lean CheckAxiomsFinitePartialSupportOrderIso.lean
python3 scripts/check_no_placeholders.py
```

No manuscript validation marker change is justified by this
general support lemma. These are internal review roles, not
human peer review.
