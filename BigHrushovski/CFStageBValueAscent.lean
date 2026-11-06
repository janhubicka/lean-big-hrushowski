import BigHrushovski.CFSelectedOldBirthBValues
import BigHrushovski.CFStageBirthOrderCoherence

/-!
# Exact complete C_F old-b-value preimages across target-stage gaps

At a finite target stage U_n the full actual birth-b-value of
an old vertex has a unique finite preimage. Under canonical
old-stage ascent U_n → U_(n+k), the complete finite preimage
is mapped ONTO the complete later preimage, not merely into it.

The proof uses only the already verified literal birth-label
identity and injectivity of the canonical stage birth map.
No global increasing map of all birth levels, no arbitrary
graph embedding, and no new target request is required.

Consequently any selected old-source map preserving the
complete finite old b-values continues to do so after arbitrary
target-stage ascent. This is precisely the functional part
of the gap step in the represented-level induction.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Under canonical old-stage ascent, every complete finite
preimage of an actual birth-b-value maps ONTO the corresponding
preimage in the later target stage. In particular no previously
born support or block vertex can be lost or added. -/
theorem stageOldBirthBValue_ascend_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    (u : (stage F K n).carrier) :
    (stageOldBirthBValue F K n u).image
      (ascend F K n k) =
    stageOldBirthBValue F K (n + k) (ascend F K n k u) := by
  classical
  have hInitial := stageOldBirthBValue_image F K n u
  have hLater := stageOldBirthBValue_image F K (n + k)
    (ascend F K n k u)
  apply Finset.image_injective (toVertex_injective F K (n + k))
  calc
    ((stageOldBirthBValue F K n u).image
        (ascend F K n k)).image (toVertex F K (n + k)) =
      (stageOldBirthBValue F K n u).image
        (toVertex F K n) := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro v hv
          exact toVertex_ascend F K n k v
    _ = birthBValue F K (toVertex F K n u) := hInitial
    _ = birthBValue F K
      (toVertex F K (n + k) (ascend F K n k u)) := by
        rw [toVertex_ascend]
    _ = (stageOldBirthBValue F K (n + k)
        (ascend F K n k u)).image (toVertex F K (n + k)) :=
      hLater.symm

/-- An arbitrary old source subtype map which preserves complete
finite birth-b-values continues to preserve them after any
number of literal target-stage inclusions. No total extension
of the old map outside the selected source is needed. -/
theorem selectedOldBirthBValues_ascend
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ)
    {U : Type*} [Fintype U] [DecidableEq U]
    (S : Finset U)
    (e : SupportCarrier U S → (stage F K n).carrier)
    (oldB : SupportCarrier U S → Finset (SupportCarrier U S))
    (hOld : ∀ u : SupportCarrier U S,
      (oldB u).image e = stageOldBirthBValue F K n (e u))
    (u : SupportCarrier U S) :
    (oldB u).image (fun w => ascend F K n k (e w)) =
      stageOldBirthBValue F K (n + k)
        (ascend F K n k (e u)) := by
  classical
  calc
    (oldB u).image (fun w => ascend F K n k (e w)) =
      ((oldB u).image e).image (ascend F K n k) := by
        rw [Finset.image_image]
        rfl
    _ = (stageOldBirthBValue F K n (e u)).image
      (ascend F K n k) := by
        rw [hOld u]
    _ = stageOldBirthBValue F K (n + k)
      (ascend F K n k (e u)) :=
        stageOldBirthBValue_ascend_image F K n k (e u)

end CFCoherentTower
end BigHrushovski
