import BigHrushovski.CFSelectedBatchLexOrder
import BigHrushovski.CFFiniteLevelOrderRigidity

/-!
# Exact identification of tagged request order with inherited stage order

The preceding simultaneous selected-batch theorem uses the
manuscript's literal comparison: old vertices first, then the
lexicographic request code (named support tuple, fresh size, full
ordered graph matrix), then the fresh ordinal.

The actual finite tower U_n has a recursively inherited linear
order. We verify that its restriction at every successor level
is *exactly* this tagged comparison, not an independently chosen
rank or order. The proof separates old-old, old-fresh, fresh-old
and fresh-fresh cases.

Consequently the actual simultaneous selected-batch map from a
source stage n to a target stage m preserves and reflects the
precise finite-stage order, even when m < n. Only the selected
old source must be embedded increasingly; no embedding of the
whole old source stage is assumed.

This completes the order aspect of the one-level finite map,
but not yet its complete b-values or the induction through
represented levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The exact request comparison is equivalent to comparison of
the canonical numerical ranks already used in the stage order. -/
theorem stageLt_fresh_iff_requestLex
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ)
    (r s : BirthRequest F K n)
    (i : Fin r.code.1.val) (j : Fin s.code.1.val) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    stageLt F K (n + 1) (Sum.inr (⟨r, i⟩ : FreshAt F K n))
      (Sum.inr (⟨s, j⟩ : FreshAt F K n)) ↔
      RequestLexLt (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r s ∨
        (r = s ∧ i.val < j.val) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  have hEq :
      stageCanonicalRank F K n r =
          stageCanonicalRank F K n s ↔ r = s := by
    constructor
    · exact (stageCanonicalRank_injective F K n)
    · intro h
      cases h
      rfl
  exact (stageOrder_fresh_iff F K n r s i j).trans
    (or_congr
      (stageCanonicalRank_comparison F K n r s).symm
      (and_congr hEq Iff.rfl))

/-- The selected tagged request-lex relation on the literal
successor carrier agrees exactly with the recursively inherited
finite-stage linear order. This is not an order on abstract
isomorphism types or an arbitrary numbered catalogue. -/
theorem taggedLexLt_stage_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ)
    (x y : (stage F K (n + 1)).carrier) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    TaggedLexLt (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) x y ↔
    stageLt F K (n + 1) x y := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          change u < v ↔
            stageLt F K (n + 1) (Sum.inl u) (Sum.inl v)
          exact (stageOrder_old_iff F K n u v).symm
      | inr v =>
          change True ↔ stageLt F K (n + 1) (Sum.inl u) (Sum.inr v)
          exact ⟨fun _ => stageOrder_old_lt_fresh F K n u v,
            fun _ => trivial⟩
  | inr u =>
      cases y with
      | inl v =>
          change False ↔ stageLt F K (n + 1) (Sum.inr u) (Sum.inl v)
          have hOldNew := stageOrder_old_lt_fresh F K n v u
          have hNot := stageLt_asymm F K (n + 1)
            (Sum.inl v) (Sum.inr u) hOldNew
          exact ⟨False.elim, fun h => (hNot h).elim⟩
      | inr v =>
          rcases u with ⟨r, i⟩
          rcases v with ⟨s, j⟩
          change
            (RequestLexLt (stage F K n).graph
                (GrowthAllowedLocal F) (fun P => K P.card) r s ∨
              (r = s ∧ i.val < j.val)) ↔
            stageLt F K (n + 1)
              (Sum.inr (⟨r, i⟩ : FreshAt F K n))
              (Sum.inr (⟨s, j⟩ : FreshAt F K n))
          exact (stageLt_fresh_iff_requestLex F K n r s i j).symm

/-- The *actual* finite-stage order is preserved and reflected
by the simultaneous selected-batch map with a prescribed old
embedding, even when the target level m is earlier than the
source level n. -/
theorem selectedGrowthBatchMap_stageOrder_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ)
    (S : Finset (stage F K n).carrier)
    (f : (stage F K n).carrier → (stage F K m).carrier)
    (hf : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMonoOn f S)
    (D : Finset (Requests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)))
    (h : SelectedGrowthTransport F K
      (stage F K n).graph (stage F K m).graph S f D)
    (x y : SelectedCarrier (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) S D) :
    stageLt F K (n + 1)
      (selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D x)
      (selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D y) ↔
    stageLt F K (m + 1)
      (selectedGrowthBatchMap F K
        (stage F K n).graph (stage F K m).graph S f hf D h x)
      (selectedGrowthBatchMap F K
        (stage F K n).graph (stage F K m).graph S f hf D h y) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  have hLex := selectedGrowthBatchMap_taggedLex_iff
    F K (stage F K n).graph (stage F K m).graph
    S f hf D h x y
  exact ((taggedLexLt_stage_iff F K n _ _).symm).trans
    (hLex.trans (taggedLexLt_stage_iff F K m _ _))

end CFCoherentTower
end BigHrushovski
