# Adversarial audit: finite b-closed sets in the countable C_F birth graph

19 October 2026

## Exact result

A vertex is literally a pair of birth level and tagged finite request ordinal. `IsBirthBlockClosed F K s` requires that whenever the finite set s contains one fresh vertex of a request at level n, it contains **all** fresh vertices of that request and every old vertex of its **literal named support**. This encodes closure under the manuscript's auxiliary operation `b(v)=P_B∪B`.

The theorem `birthBlockClosed_global_dClosed` asserts that every **finite** such set is strictly d-closed in the actual countable birth-labelled graph. It is not a claim of numerical predimension for infinite sets.

## Eight hostile reviews

1. **Exact b-values.** A block is the complete fibre of one request tag. We do not identify isomorphic supports, different requests, or their fresh ordinals; the old support is the literal one in the previous finite stage.
2. **Stage carriers.** The induction cuts s using `toVertex F K n` on each actual finite carrier. The identity `toVertex_old` ensures the old successor part is *exactly* the image of the previous cut, not just isomorphic.
3. **Fresh block saturation.** Selected requests are those with a fresh vertex in s. The b-closure assumption forces every ordinal in that selected block into s; conversely no unselected fresh vertex enters the cut. The equality of actual tagged subsets is separately audited.
4. **Old supports.** For a selected request r, every `u∈r.support` is in the previous cut, via the birth map. This is stronger than demanding only the actual old graph neighbours and exactly matches the manuscript's b(v).
5. **Strictness.** The induction invokes `taggedSupportClosedSubbatch_dClosed_full` on every successor stage, not the weak strong-factor lemma. The selected-sub-batch result itself relies on no-cross modularity and arbitrary-prefix strict closure.
6. **Countable step.** After finite-stage closure is established, a finite s is contained in one stage image. Its precise preimage is strictly d-closed in that stage, and the image is globally strictly d-closed by `finiteClosedPart_global`. No invented global predimension of an infinite set is used.
7. **Class hypotheses.** The theorem does not use the real-valued growth-function inverse, free amalgamation of the growth class, or Fraïssé genericity. These assumptions were needed for the separate construction/identification, not for the intrinsic selected-tag graph-theoretic closure.
8. **Recovery boundary.** This theorem supplies a missing input to `H(R(v))=C(v)`, but does not prove that each `C(v)` is b-closed, construct its exact finite reachable block set, or verify the full `(R,H)` versus b embedding equivalence. No marker for that proposition is promoted until these steps are combined.

The reviews are role-separated internal adversarial checks, not independent human referees. GREEN requires a complete passing Lean build, exact axiom audit and no-placeholder scan; prior successful CI of dependencies does not establish this theorem.
