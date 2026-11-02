import BigHrushovski.CFBirthBlockClosure
import BigHrushovski.CFSelectedBatchSubtypeMap

/-!
# The empty selected old source is strictly d-closed at every C_F stage

Finite level lifting may assign the first represented source level
to any natural target level, including zero. The selected old
source is then empty. Its image must still be strictly d-closed
in the target old stage to apply the same partial-source
request constructor as at subsequent represented levels.

The finite tagged tower has this property without postulating
a target vertex or totalizing a function on the ambient source
stage. It follows from the already verified strict d-closedness
of the stage cuts of b-closed finite sets, applied to the empty
birth set.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The empty birth-labelled set is closed under the complete
block-plus-old-support operation. -/
theorem empty_birthBlockClosed (F : ℕ → ℝ) (K : ℕ → ℕ) :
    IsBirthBlockClosed F K (∅ : Finset (Vertex F K)) := by
  intro n r i hi
  exact False.elim (Finset.not_mem_empty _ hi)

/-- The stage cut of the empty birth-labelled set is literally
empty at every finite stage; no distinguished old vertex occurs. -/
theorem stageCut_empty (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    stageCut F K (∅ : Finset (Vertex F K)) n = ∅ := by
  classical
  simp [stageCut]

/-- Every finite C_F tagged stage has the empty set strictly
d-closed in the ENTIRE stage, including the first stage and
all stages with a nonempty ambient old source. -/
theorem empty_dClosed_in_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    (stage F K n).graph.toPredimension.IsDClosed
      (∅ : Finset (stage F K n).carrier) Finset.univ := by
  have h := stageCut_dClosed_of_birthBlockClosed
    F K (∅ : Finset (Vertex F K))
    (empty_birthBlockClosed F K) n
  simpa only [stageCut_empty] using h

/-- The image of the unique partial map from an empty selected
old source is strictly d-closed in any target old stage.
The complete old source carrier U need not be empty. -/
theorem empty_selectedOldImage_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    {U : Type*} [Fintype U] [DecidableEq U]
    (n : ℕ)
    (e : SupportCarrier U (∅ : Finset U) →
      (stage F K n).carrier) :
    (stage F K n).graph.toPredimension.IsDClosed
      (selectedOldImage (∅ : Finset U) e) Finset.univ := by
  classical
  have hEmpty : selectedOldImage (∅ : Finset U) e = ∅ := by
    ext x
    simp [selectedOldImage]
  rw [hEmpty]
  exact empty_dClosed_in_stage F K n

end CFCoherentTower
end BigHrushovski
