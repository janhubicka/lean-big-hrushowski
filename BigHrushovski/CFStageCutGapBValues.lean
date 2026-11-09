import BigHrushovski.CFStageCutGapEquiv
import BigHrushovski.CFSelectedOldBirthBValues

/-!
# Exact complete birth-b-values across skipped C_F source levels

For a finite b-closed source, the canonical equivalence between
stage-n and stage-m source cuts across an unrepresented interval
preserves every literal countable birth label. It consequently
sends every complete finite source b-value ONTO the complete
finite value at the later cut.

Unlike a statement about the auxiliary old b-operation on an
abstract copy, this is equality of actual finite subsets of
dependent source-cut subtypes. The argument uses only the
complete b-value preimage theorem and injectivity of the
canonical stage-to-birth map; no lifting induction or target
old-stage embedding is assumed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The complete finite source b-value is literally carried
along the canonical cut equivalence across any interval
containing no represented source birth level. -/
theorem stageCutGapEquiv_completeBirthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (cutOldBirthBValue F K s n u).image
      (stageCutGapEquiv F K s n m hnm hGap) =
    cutOldBirthBValue F K s m
      (stageCutGapEquiv F K s n m hnm hGap u) := by
  classical
  let E := stageCutGapEquiv F K s n m hnm hGap
  let birthLater : SupportCarrier (stage F K m).carrier
      (stageCut F K s m) → Vertex F K :=
    fun v => toVertex F K m v.val
  have hInjective : Function.Injective birthLater := by
    intro v w hvw
    apply Subtype.ext
    exact toVertex_injective F K m hvw
  apply Finset.image_injective hInjective
  have hPush :
      ((cutOldBirthBValue F K s n u).image E).image birthLater =
      (cutOldBirthBValue F K s n u).image
        (fun v => toVertex F K n v.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
      obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      calc
        toVertex F K n a.val = toVertex F K m (E a).val :=
          (stageCutGapEquiv_birth F K s n m hnm hGap a).symm
        _ = toVertex F K m w.val := by rw [haw]
        _ = v := hwv
    · intro hv
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨E a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · calc
          toVertex F K m (E a).val = toVertex F K n a.val :=
            stageCutGapEquiv_birth F K s n m hnm hGap a
          _ = v := hav
  calc
    ((cutOldBirthBValue F K s n u).image E).image birthLater =
      (cutOldBirthBValue F K s n u).image
        (fun v => toVertex F K n v.val) := hPush
    _ = birthBValue F K (toVertex F K n u.val) :=
      cutOldBirthBValue_image F K s hs n u
    _ = birthBValue F K (toVertex F K m (E u).val) := by
      rw [stageCutGapEquiv_birth F K s n m hnm hGap u]
    _ = (cutOldBirthBValue F K s m (E u)).image birthLater :=
      (cutOldBirthBValue_image F K s hs m (E u)).symm

end CFCoherentTower
end BigHrushovski
