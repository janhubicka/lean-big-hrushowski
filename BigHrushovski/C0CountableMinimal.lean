import BigHrushovski.C0TraceStages

/-!
# One countable enumeration by minimal strong closure-components

The strong C0 skeleton has successive finite globally strong stages,
with each strict interval refined by a nonempty finite minimal trace.
The positive lengths determine unique half-open arithmetic blocks.
We choose the stage after the local number of steps inside the block.

The terminal stage of one trace equals the initial stage of the
next trace; the endpoint is included *only once*, at the beginning
of the next block. The two cases in the successor proof are an
internal step and the last step of a finite trace.

This proves the existence of the countable minimal strong
enumeration of the underlying generic graph. It does not
formalize the unary closure function, the age of its functional
presentation, or a Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteCatalogue

private abbrev offsets :=
  Predimension.C0Offsets.offset genericC0SegmentLength

/-- The source stage of the genuine minimal strong step indexed by i.
Every natural number falls in one of the nonempty finite traces. -/
noncomputable def genericC0MinimalStage (i : ℕ) : Finset ℕ :=
  (genericC0SegmentTrace (genericC0BlockIndex i)).stageAt
    (i - offsets (genericC0BlockIndex i))

theorem genericC0BlockIndex_at_offset (n : ℕ) :
    genericC0BlockIndex (offsets n) = n := by
  apply Predimension.C0Offsets.block_eq_of_interval
    genericC0SegmentLength genericC0SegmentLength_pos
    (offsets n) n
  · exact le_rfl
  · rw [Predimension.C0Offsets.offset_succ]
    have hp := genericC0SegmentLength_pos n
    omega

/-- Every skeleton stage appears as the first genuine stage of its
finite minimal-refinement interval. -/
theorem genericC0MinimalStage_at_offset (n : ℕ) :
    genericC0MinimalStage (offsets n) =
      genericC0StrongSkeleton.stage n := by
  unfold genericC0MinimalStage
  rw [genericC0BlockIndex_at_offset]
  simp only [Nat.sub_self]
  exact Predimension.MinimalStrongTrace.stageAt_zero
    (genericC0SegmentTrace n)

/-- A single omega-indexed sequence of genuinely minimal strong
steps. At block boundaries the terminal stage of one finite trace
equals the source stage of the following trace; no dummy equality
step has been inserted. -/
theorem genericC0MinimalStage_minimal_step (i : ℕ) :
    Predimension.IsMinimalStrongStep
      genericTwoSparseGraph.toPredimension
      (genericC0MinimalStage i) (genericC0MinimalStage (i + 1)) := by
  let n := genericC0BlockIndex i
  let j := i - offsets n
  have hlo : offsets n ≤ i :=
    (genericC0BlockIndex_bounds i).1
  have hj : j < genericC0SegmentLength n :=
    genericC0LocalIndex_lt i
  have hStep :=
    Predimension.MinimalStrongTrace.stageAt_minimal_step
      (genericC0SegmentTrace n) j hj
  have hAtI :
      genericC0MinimalStage i =
        (genericC0SegmentTrace n).stageAt j := rfl
  by_cases hInside : j + 1 < genericC0SegmentLength n
  · have hNextUpper : i + 1 < offsets (n + 1) := by
      rw [Predimension.C0Offsets.offset_succ]
      dsimp [j] at hInside
      omega
    have hNextBlock : genericC0BlockIndex (i + 1) = n :=
      Predimension.C0Offsets.block_eq_of_interval
        genericC0SegmentLength genericC0SegmentLength_pos
        (i + 1) n (by omega) hNextUpper
    have hjNext : i + 1 - offsets n = j + 1 := by
      dsimp [j]
      omega
    have hAtNext :
        genericC0MinimalStage (i + 1) =
          (genericC0SegmentTrace n).stageAt (j + 1) := by
      unfold genericC0MinimalStage
      rw [hNextBlock, hjNext]
    rw [hAtI, hAtNext]
    exact hStep
  · have hBoundary : j + 1 = genericC0SegmentLength n := by
      omega
    have hNextOffset : i + 1 = offsets (n + 1) := by
      rw [Predimension.C0Offsets.offset_succ]
      dsimp [j] at hBoundary
      omega
    have hAtNext :
        genericC0MinimalStage (i + 1) =
          genericC0StrongSkeleton.stage (n + 1) := by
      rw [hNextOffset]
      exact genericC0MinimalStage_at_offset (n + 1)
    have hAtEnd :
        (genericC0SegmentTrace n).stageAt (j + 1) =
          genericC0StrongSkeleton.stage (n + 1) := by
      rw [hBoundary]
      exact Predimension.MinimalStrongTrace.stageAt_last
        (genericC0SegmentTrace n)
    rw [hAtI, hAtNext, ← hAtEnd]
    exact hStep

/-- The flattened countable enumeration is a genuine strong chain,
not merely an increasing set family. -/
noncomputable def genericC0MinimalStrongChain :
    Predimension.StrongChain genericTwoSparseGraph.toPredimension where
  stage := genericC0MinimalStage
  strong_step := fun n => (genericC0MinimalStage_minimal_step n).1
  covers := by
    intro v
    obtain ⟨n, hn⟩ := genericC0StrongSkeleton.covers v
    refine ⟨offsets n, ?_⟩
    rw [genericC0MinimalStage_at_offset]
    exact hn

theorem genericC0MinimalStage_global (i : ℕ) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (genericC0MinimalStage i) :=
  genericC0MinimalStrongChain.stage_global i

theorem genericC0MinimalStage_strict (i : ℕ) :
    genericC0MinimalStage i ⊂ genericC0MinimalStage (i + 1) :=
  Finset.ssubset_iff_subset_ne.mpr
    ⟨(genericC0MinimalStage_minimal_step i).1.1,
      (genericC0MinimalStage_minimal_step i).2.1⟩

/-- Every vertex of a new component generates the same closure
over the old prefix, even when it is not the temporary generator. -/
theorem genericC0MinimalStage_equal_closure
    (i : ℕ) (x : ℕ)
    (hxB : x ∈ genericC0MinimalStage (i + 1))
    (hxA : x ∉ genericC0MinimalStage i) :
    genericStrongClosure (insert x (genericC0MinimalStage i)) =
      genericC0MinimalStage (i + 1) :=
  genericStrongExhaustion.minimal_step_generated_by_every_new_vertex
    (genericC0MinimalStage_minimal_step i)
    (genericC0MinimalStage_global (i + 1)) hxB hxA

end FiniteCatalogue
end BigHrushovski
