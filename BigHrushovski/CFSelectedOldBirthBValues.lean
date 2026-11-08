import BigHrushovski.CFBirthBValues
import BigHrushovski.CFBirthGeneratedClosure
import BigHrushovski.CFBirthBlockClosure

/-!
# Complete old birth-b-values on literal C_F finite source cuts

The recursive one-level functional embedding transports a family
of finite auxiliary b-values on the selected old subtype.  Here
we recover these values directly from the actual countable
birth-labelled b-operation, with no additional valuation or
choice of a copied finite graph.

For a b-closed finite source s, each old vertex's complete
birth-b-value lies in the literal cut of s at any stage
containing that vertex.  This follows by applying b-closure to
both s and the entire finite stage image.  It gives exact
preimage finite sets on the selected old subtype and the whole
target old stage.

The final equivalence identifies the old-b-value induction
hypothesis in the one-level lemma with preservation of the
actual countable birth-b-value, *not* an arbitrary surrogate.
It does not produce that hypothesis from nothing.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The complete actual birth-b-value of a selected OLD source
vertex, pulled back to the literal selected finite old subtype.
This is the predecessor value needed by one-level lifting. -/
noncomputable def cutOldBirthBValue
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    Finset (SupportCarrier (stage F K n).carrier (stageCut F K s n)) := by
  classical
  exact Finset.univ.filter (fun w =>
    toVertex F K n w.val ∈ birthBValue F K (toVertex F K n u.val))

/-- Every old selected source b-value is represented exactly
inside its literal old selected subtype. Both the WHOLE support
and WHOLE fresh block of the vertex are retained. -/
theorem cutOldBirthBValue_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (cutOldBirthBValue F K s n u).image
      (fun w => toVertex F K n w.val) =
    birthBValue F K (toVertex F K n u.val) := by
  classical
  have huSource : toVertex F K n u.val ∈ s :=
    (mem_stageCut_iff F K s n u.val).mp u.property
  have huStage : toVertex F K n u.val ∈ stageImage F K n :=
    Finset.mem_image.mpr ⟨u.val, Finset.mem_univ _, rfl⟩
  have hInSource :
      birthBValue F K (toVertex F K n u.val) ⊆ s :=
    birthBValue_subset_of_closed F K s hs huSource
  have hInStage :
      birthBValue F K (toVertex F K n u.val) ⊆ stageImage F K n :=
    birthBValue_subset_of_closed F K (stageImage F K n)
      (stageImage_birthBlockClosed F K n) huStage
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    have hwB : toVertex F K n w.val ∈
        birthBValue F K (toVertex F K n u.val) :=
      (Finset.mem_filter.mp hw).2
    rw [← hwv]
    exact hwB
  · intro hv
    obtain ⟨w, _, hwv⟩ := Finset.mem_image.mp (hInStage hv)
    have hwSource : w ∈ stageCut F K s n :=
      (mem_stageCut_iff F K s n w).mpr (by
        rw [hwv]
        exact hInSource hv)
    refine Finset.mem_image.mpr ⟨⟨w, hwSource⟩, ?_, hwv⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · change toVertex F K n w ∈
        birthBValue F K (toVertex F K n u.val)
      rw [hwv]
      exact hv

/-- The complete b-value of an arbitrary target old-stage
vertex, pulled back to the full finite target stage carrier. -/
noncomputable def stageOldBirthBValue
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (u : (stage F K n).carrier) :
    Finset (stage F K n).carrier := by
  classical
  exact Finset.univ.filter (fun w =>
    toVertex F K n w ∈ birthBValue F K (toVertex F K n u))

/-- Every complete target old b-value is represented exactly
in its finite target stage, with no vertices left outside it. -/
theorem stageOldBirthBValue_image
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (u : (stage F K n).carrier) :
    (stageOldBirthBValue F K n u).image (toVertex F K n) =
      birthBValue F K (toVertex F K n u) := by
  classical
  have huStage : toVertex F K n u ∈ stageImage F K n :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hInStage :
      birthBValue F K (toVertex F K n u) ⊆ stageImage F K n :=
    birthBValue_subset_of_closed F K (stageImage F K n)
      (stageImage_birthBlockClosed F K n) huStage
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    rw [← hwv]
    exact (Finset.mem_filter.mp hw).2
  · intro hv
    obtain ⟨w, _, hwv⟩ := Finset.mem_image.mp (hInStage hv)
    refine Finset.mem_image.mpr ⟨w, ?_, hwv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hwv]
      exact hv⟩

/-- The one-level OLD-value hypothesis is equivalent to exact
transport of the actual complete birth-b-value of each source
old vertex. The target full-stage value cannot have extra
vertices outside the image when the equality holds.

The old source is a genuine subtype. No total map of its
ambient stage into the target stage is assumed. -/
theorem oldBValue_image_iff_birthBValue
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    (cutOldBirthBValue F K s n u).image e =
      stageOldBirthBValue F K m (e u) ↔
    (cutOldBirthBValue F K s n u).image
      (fun w => toVertex F K m (e w)) =
      birthBValue F K (toVertex F K m (e u)) := by
  classical
  have hTarget := stageOldBirthBValue_image F K m (e u)
  have hCompose :
      ((cutOldBirthBValue F K s n u).image e).image
        (toVertex F K m) =
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K m (e w)) := by
    rw [Finset.image_image]
    rfl
  constructor
  · intro hOld
    calc
      (cutOldBirthBValue F K s n u).image
          (fun w => toVertex F K m (e w)) =
        ((cutOldBirthBValue F K s n u).image e).image
          (toVertex F K m) := hCompose.symm
      _ = (stageOldBirthBValue F K m (e u)).image
          (toVertex F K m) := by rw [hOld]
      _ = birthBValue F K (toVertex F K m (e u)) := hTarget
  · intro hBirth
    apply Finset.image_injective (toVertex_injective F K m)
    calc
      ((cutOldBirthBValue F K s n u).image e).image
          (toVertex F K m) =
        (cutOldBirthBValue F K s n u).image
          (fun w => toVertex F K m (e w)) := hCompose
      _ = birthBValue F K (toVertex F K m (e u)) := hBirth
      _ = (stageOldBirthBValue F K m (e u)).image
          (toVertex F K m) := hTarget.symm

end CFCoherentTower
end BigHrushovski
