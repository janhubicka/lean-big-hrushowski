import BigHrushovski.C0ClosedBaseFrontload

/-!
# Minimal strongness when exactly one canonical component remains

The closed-base frontloading theorem is stronger than merely proving
strongness of a finite closed subset. If the complement of that subset
is exactly one complete canonical component, frontloading keeps its
index fibre intact and places the closed subset before it.

At the unique nonempty remaining step we obtain a minimal strong
extension from the closed subset to the whole graph. This is the
finite ingredient needed for enumerating countably many intrinsic
closure-components, without selecting an order between incomparable
components or a generating vertex inside a component.

This theorem is stated for a finite canonical component presentation,
and does not use a countable genericity hypothesis.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- Let s be closed under the complete canonical unary values of a
finite graph with a possibly empty-slot minimal strong component
presentation. If every vertex outside s belongs to exactly one
component (the component of x), then adjoining it is a minimal
strong step. The conclusion has no choice of component chronology. -/
theorem closed_complement_one_component_minimal
    (G : GraphOn V) (κ : V → Fin n)
    (hSteps : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (x : V)
    (hComplement :
      (Finset.univ : Finset V) \ s = component κ (κ x).val) :
    G.toPredimension.IsMinimalStrongStep s Finset.univ := by
  classical
  let j : ℕ := (κ x).val
  have hj : j < n := (κ x).isLt
  have hxOutside : x ∉ s := by
    have hxComp : x ∈ component κ j :=
      (mem_component_iff κ j x).mpr rfl
    have hxOut : x ∈ (Finset.univ : Finset V) \ s := by
      rw [hComplement]
      exact hxComp
    exact (Finset.mem_sdiff.mp hxOut).2
  have hEarlier : oldStage κ j ⊆ s := by
    intro v hv
    by_contra hvNot
    have hvOut : v ∈ (Finset.univ : Finset V) \ s :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvNot⟩
    rw [hComplement] at hvOut
    have hvIndex : (κ v).val = j :=
      (mem_component_iff κ j v).mp hvOut
    have hvEarlier : (κ v).val < j :=
      (mem_oldStage_iff κ j v).mp hv
    omega
  have hFirst :
      oldStage (frontloadIndex κ s) (n+j) = s := by
    rw [oldStage_frontload_after κ s j]
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvS | hvEarlier
      · exact hvS
      · exact hEarlier hvEarlier
    · intro hv
      exact Finset.mem_union.mpr (Or.inl hv)
  have hLast :
      oldStage (frontloadIndex κ s) (n+j+1) =
        (Finset.univ : Finset V) := by
    have hIndexEq : n+j+1 = n+(j+1) := by omega
    rw [hIndexEq, oldStage_frontload_after κ s (j+1)]
    ext v
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      by_cases hvS : v ∈ s
      · exact Finset.mem_union.mpr (Or.inl hvS)
      · have hvOut : v ∈ (Finset.univ : Finset V) \ s :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩
        rw [hComplement] at hvOut
        have hvIndex : (κ v).val = j :=
          (mem_component_iff κ j v).mp hvOut
        have hvEarlier : v ∈ oldStage κ (j+1) :=
          (mem_oldStage_iff κ (j+1) v).mpr (by omega)
        exact Finset.mem_union.mpr (Or.inr hvEarlier)
  have hStep := frontloadIndex_minimal_steps
    G κ s hClosed hSteps (n+j) (by omega)
  rcases hStep with hEq | hMin
  · have hsAll : s = (Finset.univ : Finset V) := by
      calc
        s = oldStage (frontloadIndex κ s) (n+j) := hFirst.symm
        _ = oldStage (frontloadIndex κ s) (n+j+1) := hEq
        _ = Finset.univ := hLast
    have hxS : x ∈ s := by
      rw [hsAll]
      exact Finset.mem_univ _
    exact (hxOutside hxS).elim
  · rw [hFirst, hLast] at hMin
    exact hMin

end FiniteC0
end BigHrushovski
