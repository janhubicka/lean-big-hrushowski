import BigHrushovski.CFSelectedBirthBValueBridge
import BigHrushovski.CFSelectedOldBirthBValues
import BigHrushovski.CFSelectedCutEquiv
import BigHrushovski.CFPartialOneLevelFunctional

/-!
# Identify selected one-level auxiliary b-values with actual source cuts

The selected one-level functional map is parametrized by old
finite b-values.  On a finite b-closed source, those old values
have a unique literal representation as preimages of the true
countable birthBValue.  For fresh vertices, the selected value
is the complete support plus the WHOLE fresh block.

We prove that for EVERY old or fresh vertex in a selected level
the selected one-level value maps exactly onto its complete
actual birthBValue, via the literal stage inclusion.

Using the established equivalence between the selected carrier
and the actual next stage cut, we also identify this value
with the canonical finite old-b-value preimage on the ACTUAL
next cut, not just with a separately named auxiliary operation.

No full multi-level lift or arbitrary-embedding uniqueness is
claimed here; this is an exact finite set equality.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Under the literal selected-source stage map, the complete
one-level value of EVERY selected old or new vertex is exactly
its complete actual countable birth-b-value. The old values
are the unique finite source-cut preimages of birthBValue. -/
theorem selectedCut_oneLevelBValue_birth_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ)
    (x : CutSelectedCarrier F K s n) :
    (selectedOneLevelBValue (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
      (fun r =>
        selectedRequests_support_subset_stageCut F K s hs n
          r.val r.property)
      (cutOldBirthBValue F K s n) x).image
      (fun z =>
        toVertex F K (n + 1)
          (selectedSourceMap (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card)
            (stageCut F K s n) (selectedRequests F K s n) z)) =
    birthBValue F K
      (toVertex F K (n + 1)
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          (stageCut F K s n) (selectedRequests F K s n) x)) := by
  classical
  cases x with
  | inl u =>
      change
        ((cutOldBirthBValue F K s n u).image
          (fun w : SupportCarrier (stage F K n).carrier
            (stageCut F K s n) =>
              (Sum.inl w : CutSelectedCarrier F K s n))).image
            (fun z =>
              toVertex F K (n + 1)
                (selectedSourceMap (stage F K n).graph
                  (GrowthAllowedLocal F) (fun P => K P.card)
                  (stageCut F K s n) (selectedRequests F K s n) z)) =
        birthBValue F K (toVertex F K n u.val)
      calc
        _ = (cutOldBirthBValue F K s n u).image
              (fun w => toVertex F K n w.val) := by
              rw [Finset.image_image]
              rfl
        _ = _ := cutOldBirthBValue_image F K s hs n u
  | inr z =>
      rcases z with ⟨r, i⟩
      change
        (selectedBlockBValue (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          (stageCut F K s n) (selectedRequests F K s n)
          r (selectedRequests_support_subset_stageCut F K s hs n
            r.val r.property)).image
          (fun z =>
            toVertex F K (n + 1)
              (selectedSourceMap (stage F K n).graph
                (GrowthAllowedLocal F) (fun P => K P.card)
                (stageCut F K s n) (selectedRequests F K s n) z)) =
        birthBValue F K (⟨n, ⟨r.val, i⟩⟩ : Vertex F K)
      exact (selectedFresh_birthBValue_source F K n
        (stageCut F K s n) (selectedRequests F K s n)
        r (selectedRequests_support_subset_stageCut F K s hs n
          r.val r.property) i).symm

/-- Under the CANONICAL equivalence from the selected carrier to
the actual stage-(n+1) cut, the complete one-level b-value
is exactly the finite preimage of the true birth-b-value of
that vertex. The source set is not merely isomorphic: it is
identified with the actual literal source cut. -/
theorem selectedCut_oneLevelBValue_eq_actualCut
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ)
    (x : CutSelectedCarrier F K s n) :
    (selectedOneLevelBValue (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
      (fun r =>
        selectedRequests_support_subset_stageCut F K s hs n
          r.val r.property)
      (cutOldBirthBValue F K s n) x).image
        (selectedCutEquiv F K s hs n) =
      cutOldBirthBValue F K s (n + 1)
        (selectedCutEquiv F K s hs n x) := by
  classical
  let B := selectedOneLevelBValue (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card)
    (stageCut F K s n) (selectedRequests F K s n)
    (fun r =>
      selectedRequests_support_subset_stageCut F K s hs n
        r.val r.property)
    (cutOldBirthBValue F K s n) x
  have hSource :
      B.image (fun z =>
        toVertex F K (n + 1)
          (selectedSourceMap (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card)
            (stageCut F K s n) (selectedRequests F K s n) z)) =
      birthBValue F K
        (toVertex F K (n + 1)
          (selectedSourceMap (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card)
            (stageCut F K s n) (selectedRequests F K s n) x)) :=
    selectedCut_oneLevelBValue_birth_image F K s hs n x
  have hCut := cutOldBirthBValue_image F K s hs (n + 1)
    (selectedCutEquiv F K s hs n x)
  have hInjective : Function.Injective
      (fun y : SupportCarrier (stage F K (n + 1)).carrier
        (stageCut F K s (n + 1)) => toVertex F K (n + 1) y.val) := by
    intro a b hab
    exact Subtype.ext ((toVertex_injective F K (n + 1)) hab)
  apply Finset.image_injective hInjective
  calc
    (B.image (selectedCutEquiv F K s hs n)).image
        (fun y : SupportCarrier (stage F K (n + 1)).carrier
          (stageCut F K s (n + 1)) => toVertex F K (n + 1) y.val) =
      B.image (fun z =>
        toVertex F K (n + 1)
          (selectedSourceMap (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card)
            (stageCut F K s n) (selectedRequests F K s n) z)) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z hz
      exact congrArg (toVertex F K (n + 1))
        (selectedCutEquiv_val F K s hs n z)
    _ = birthBValue F K
      (toVertex F K (n + 1)
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          (stageCut F K s n) (selectedRequests F K s n) x)) := hSource
    _ = birthBValue F K
      (toVertex F K (n + 1)
        (selectedCutEquiv F K s hs n x).val) := by
      rw [selectedCutEquiv_val]
    _ = (cutOldBirthBValue F K s (n + 1)
        (selectedCutEquiv F K s hs n x)).image
          (fun y : SupportCarrier (stage F K (n + 1)).carrier
            (stageCut F K s (n + 1)) => toVertex F K (n + 1) y.val) :=
      hCut.symm

end CFCoherentTower
end BigHrushovski
