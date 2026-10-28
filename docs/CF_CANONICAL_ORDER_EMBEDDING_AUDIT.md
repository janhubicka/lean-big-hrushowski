# Adversarial audit: literal C_F closed-source embeddings with the canonical order

28 October 2026

## Claim

The existing Lean theorem `literalClosedSource_bValues_iff_RHValues_of_chosenOrder`
required a supplied strict order and the hypothesis that its restriction
to each complete birth block agreed with the finite fresh ordinals.

The new recursively constructed `canonicalBirthLt` now carries the exact
support-tuple/fresh-size/full-adjacency request comparison in the manuscript.
Its compatibility with the order inside every complete fresh block is a
proved theorem. Instantiating the old value-equivalence theorem with this
particular order eliminates the remaining *presentation* hypothesis.

## Independent hostile checks

1. **Order identity:** The order passed to the theorem is the actual
   `canonicalBirthLt`, based on `stageCanonicalRank`; it is not an
   arbitrary unrelated order on the same countable carrier.
2. **Complete values:** The b-side is equality of the entire image
   of each named finite unary value, not mere preservation of its
   generators. The reverse side is full R-value transport and full
   H-value transport on all finite root sets.
3. **Partial function domain:** The third right-side conjunct reflects
   root status of all finite sets; preservation of values on the
   already-defined domain alone would not establish a functional
   embedding.
4. **Empty and infinite sources:** The map's literal source subtype
   can be empty or infinite. The auxiliary extension to the ambient
   carrier is used only to express image formulas, with its properties
   discharged on the source subtype.
5. **Embedding hypotheses:** The theorem still assumes injectivity,
   complete induced adjacency, reflection/preservation of the birth
   level preorder, and the *actual* canonical order. It does not
   infer these from arbitrary injective maps.
6. **No false genericity:** Finite unique level lifting and countable
   embedding monoid identification are not conclusions of this
   theorem. The C_F growth/function hypotheses remain as specified
   in earlier construction modules.

## Verification contract

One exact axiom endpoint is added to CheckAxioms.lean. Successful full
CI and standard-axiom and placeholder checks are necessary before
promoting the manuscript's root recovery proposition to fully Lean
verified. The review is a collection of separate mathematical
failure-mode checks, not a claim to independent human reviewers.
