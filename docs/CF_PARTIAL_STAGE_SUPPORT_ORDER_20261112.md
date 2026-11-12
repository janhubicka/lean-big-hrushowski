# Track B: exact ordered stage support from a partial birth map

12 November 2026. This is the bridge between equality of birth
supports and the finite-stage order isomorphisms required by the
one-level target request code theorem.

For any selected old-stage support P⊆U_n with literal birth image
inside the finite source s, a partial map e:s→M_F^† whose exact
image of P is the birth image of Q⊆U_m and which preserves
the canonical birth order determines an order isomorphism
P≃oQ. The source/target ambient stages need not embed
into each other and no level-map extension is required.

## Six internal adversarial referee roles

1. **Literal source names.** The map from each p∈P to the
   finite source is `toVertex F K n p`; membership is
   justified by the explicit containment of the entire
   birth image of P in s, not by a chosen isomorphic copy.
2. **Literal target names.** For each source support point,
   exact image equality supplies a target point q∈Q with
   `toVertex F K m q=e(toVertex F K n p)`.
   Injectivity of the target-stage birth map makes q unique.
3. **No total-stage hypothesis.** The map e is called only
   on the actual selected source support and the surjectivity
   proof only on Q. In particular this remains meaningful
   for the empty target old stage U_0 and empty P,Q.
4. **Order transport.** The proof uses the established
   equivalence between the recursive finite-stage order
   and the actual countable canonical birth order on both
   stages. An arbitrary unrelated linear order would not
   justify strict monotonicity.
5. **Surjectivity and nonedges.** Surjectivity uses equality,
   not inclusion, of the complete image of the selected
   support. This lemma concerns only order coordinates;
   induced adjacency of the full local request is a
   separate premise in the request-code rigidity theorem.
6. **Remaining bridge.** Exact image of named birth supports
   follows from complete b-values and birth-level preorder.
   The literal equalities in PR #436 identify them with
   the stage support images P and Q. A subsequent lemma
   must discharge this interface for an arbitrary finite
   R/H embedding, then derive all adjacency matrix bits.
   The finite uniqueness induction is not yet verified.

The above are adversarial internal mathematical checks, not
external human peer review. No manuscript GREEN marker changes.

## Exact verification

```sh
lake build BigHrushovski.CFPartialStageSupportOrder
lake env lean CheckAxiomsCFTrackBPartialStageSupportOrder.lean
python3 scripts/check_no_placeholders.py
```
