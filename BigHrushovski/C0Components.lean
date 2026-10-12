import BigHrushovski.C0EmptyBase

/-!
# Components of the countable C0 minimal strong enumeration

The strict countable minimal chain starts at ∅ and exhausts ℕ.
Each vertex consequently belongs to exactly one nonempty finite
increment B_n = A_(n+1) \ A_n.

The index of a vertex is the least natural n for which it has
entered A_(n+1). This is not an extra enumeration order inside
the finite components. The resulting partition is the starting
point for defining back-edge dependencies and the unary
component-closure presentation.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The finite nonempty increment from the n-th minimal strong stage. -/
noncomputable def genericC0Component (n : ℕ) : Finset ℕ :=
  genericC0MinimalStage (n + 1) \ genericC0MinimalStage n

theorem genericC0Component_nonempty (n : ℕ) :
    (genericC0Component n).Nonempty := by
  have hstrict := genericC0MinimalStage_strict n
  have hsub : genericC0MinimalStage n ⊆
      genericC0MinimalStage (n + 1) :=
    (Finset.ssubset_iff_subset_ne.mp hstrict).1
  have hne : genericC0MinimalStage n ≠
      genericC0MinimalStage (n + 1) :=
    (Finset.ssubset_iff_subset_ne.mp hstrict).2
  by_contra hEmpty
  have hBack : genericC0MinimalStage (n + 1) ⊆
      genericC0MinimalStage n := by
    intro x hx
    by_contra hxNot
    exact hEmpty ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxNot⟩⟩
  exact hne (le_antisymm hsub hBack)

/-- Exhaustion gives a finite first stage containing every vertex. -/
theorem genericC0_exists_component_index (x : ℕ) :
    ∃ n : ℕ, x ∈ genericC0MinimalStage (n + 1) := by
  obtain ⟨n, hn⟩ := genericC0MinimalStage_exhaustive x
  refine ⟨n, ?_⟩
  exact (genericC0MinimalStrongChain.stage_monotone
    (Nat.le_succ n)) hn

/-- First component index of a vertex in the graph enumeration. -/
noncomputable def genericC0ComponentIndex (x : ℕ) : ℕ :=
  Nat.find (genericC0_exists_component_index x)

theorem genericC0ComponentIndex_spec (x : ℕ) :
    x ∈ genericC0MinimalStage (genericC0ComponentIndex x + 1) :=
  Nat.find_spec (genericC0_exists_component_index x)

/-- The vertex was not already in the preceding closed prefix. -/
theorem genericC0ComponentIndex_not_prior (x : ℕ) :
    x ∉ genericC0MinimalStage (genericC0ComponentIndex x) := by
  by_cases hzero : genericC0ComponentIndex x = 0
  · rw [hzero, genericC0MinimalStage_zero]
    simp
  · have hpred : genericC0ComponentIndex x - 1 <
        genericC0ComponentIndex x := by omega
    have hmin : ¬ x ∈ genericC0MinimalStage
        (genericC0ComponentIndex x - 1 + 1) := by
      exact Nat.find_min (genericC0_exists_component_index x)
        (by simpa only [genericC0ComponentIndex] using hpred)
    have hEq : genericC0ComponentIndex x - 1 + 1 =
        genericC0ComponentIndex x := by omega
    rwa [hEq] at hmin

theorem genericC0ComponentIndex_mem (x : ℕ) :
    x ∈ genericC0Component (genericC0ComponentIndex x) :=
  Finset.mem_sdiff.mpr
    ⟨genericC0ComponentIndex_spec x,
      genericC0ComponentIndex_not_prior x⟩

/-- The increments form the literal partition of the generic's
vertices, not merely a cover up to infinitely many overlaps. -/
theorem genericC0ComponentIndex_eq_iff (x n : ℕ) :
    genericC0ComponentIndex x = n ↔
      x ∈ genericC0Component n := by
  constructor
  · intro h
    rw [← h]
    exact genericC0ComponentIndex_mem x
  · intro hx
    have hxNew : x ∈ genericC0MinimalStage (n + 1) :=
      (Finset.mem_sdiff.mp hx).1
    have hxOld : x ∉ genericC0MinimalStage n :=
      (Finset.mem_sdiff.mp hx).2
    have hIndexLe : genericC0ComponentIndex x ≤ n :=
      Nat.find_min' (genericC0_exists_component_index x) hxNew
    have hIndexGe : n ≤ genericC0ComponentIndex x := by
      by_contra h
      have hlt : genericC0ComponentIndex x + 1 ≤ n := by omega
      have hMono := genericC0MinimalStrongChain.stage_monotone hlt
      exact hxOld (hMono (genericC0ComponentIndex_spec x))
    omega

theorem genericC0Components_disjoint {n m : ℕ} (hne : n ≠ m) :
    Disjoint (genericC0Component n) (genericC0Component m) := by
  apply Finset.disjoint_left.mpr
  intro v hvn hvm
  have hn := (genericC0ComponentIndex_eq_iff v n).mpr hvn
  have hm := (genericC0ComponentIndex_eq_iff v m).mpr hvm
  exact hne (hn.symm.trans hm)

end FiniteCatalogue
end BigHrushovski
