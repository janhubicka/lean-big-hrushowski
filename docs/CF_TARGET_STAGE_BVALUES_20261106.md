# Track B adversarial audit — complete old b-values across target gaps

6 November 2026. Internal hostile mathematical reviewer roles,
not reports from independent human referees.

## Exact result

For any actual finite target stages U_n ⊆ U_(n+k), the
canonical `ascend` map sends the FULL finite preimage of the
complete birth-b-value of a vertex u∈U_n ONTO the full
preimage of the birth-b-value of its later representative.

This is the precise finite-set equality

    ascend[stageOldBirthBValue(n,u)] =
       stageOldBirthBValue(n+k,ascend(u)).

It follows because birth labels and complete countable birth
values are LITERALLY unchanged by the canonical old-stage
inclusion, and `toVertex` is injective at each stage.

Consequently any partial old map e:S→U_n preserving all
source complete old birth values also preserves them after
`ascend ∘ e : S→U_(n+k)`; no map on U\S is required.

## Independent adversarial roles

1. **Full-value referee:** equality holds for the entire
   finite preimage of b(v), including every old support
   vertex and every fresh-block vertex, not just an
   inclusion or list of generating neighbours.
2. **Freshness referee:** all members of b(u) were born
   before stage n when u is old there; this is established
   by the existing stage image b-closure proof, not guessed.
3. **Injection referee:** reflecting equality of finite
   target preimages uses injectivity of the later
   `toVertex F K (n+k)`. A noninjective map would
   invalidate the inference.
4. **Empty stage referee:** n=0, k=0 and stages with empty
   old carriers are included. No distinguished vertex
   or nonempty-target hypothesis is required.
5. **Arbitrary gap referee:** k is any natural number.
   No assumption of adjacent represented source levels
   or extension of a finite level assignment to ω.
6. **Literal map referee:** `ascend` is repeated Sum.inl
   from the verified tower, not an arbitrary graph copy.
7. **Partial source referee:** `selectedOldBirthBValues_ascend`
   applies to a genuine selected subtype map e:S→U_n,
   never to a total extension of e outside S.
8. **Induction referee:** this proves preservation of the
   OLD VALUE premise across target-stage gaps. It does
   not itself construct target request tags at new
   represented levels or prove uniqueness of any lift.
9. **Kernel referee:** exactly two axiom endpoints are
   imported into standalone `CheckAxiomsCFTrackBStageB.lean`.
   Full Lean build, axiom/placeholder audit and finite
   regressions are required for verification.
10. **Manuscript referee:** no mathematical prose or green
    validation marker is changed here. The complete
    finite lifting lemma remains partial until the
    represented-level induction is assembled and audited.

The proof does not need strict d-closedness; that property
is transported separately by the target stage-ascent
lemma in pending PR #320.
