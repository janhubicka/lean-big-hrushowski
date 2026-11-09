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

/-- Two finite unary-closed sets with exactly one intrinsic component
between them form a minimal strong step. The closed larger set z is
frontloaded first, and then the smaller closed set s is frontloaded
inside it; other components of G are not allowed to intervene. -/
theorem closed_one_component_interval_minimal
    (G : GraphOn V) (κ : V → Fin n)
    (hSteps : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1)))
    (s z : Finset V) (hsz : s ⊆ z)
    (hClosedS : G.IsClosedUnderValues (canonicalValue G κ) s)
    (hClosedZ : G.IsClosedUnderValues (canonicalValue G κ) z)
    (x : V)
    (hDifference : z \ s = component κ (κ x).val) :
    G.toPredimension.IsMinimalStrongStep s z := by
  classical
  let a : V → Fin (n+n) := frontloadIndex κ z
  let b : V → Fin ((n+n)+(n+n)) := frontloadIndex a s
  let j : ℕ := (κ x).val
  let k : ℕ := (n+n)+j
  have hj : j < n := (κ x).isLt
  have hxComponent : x ∈ component κ j :=
    (mem_component_iff κ j x).mpr rfl
  have hxDiff : x ∈ z \ s := by
    rw [hDifference]
    exact hxComponent
  have hxZ : x ∈ z := (Finset.mem_sdiff.mp hxDiff).1
  have hxNotS : x ∉ s := (Finset.mem_sdiff.mp hxDiff).2
  have hIndex : ∀ v : V, v ∈ z → v ∉ s → (κ v).val = j := by
    intro v hvZ hvS
    have hv : v ∈ z \ s := Finset.mem_sdiff.mpr ⟨hvZ, hvS⟩
    rw [hDifference] at hv
    exact (mem_component_iff κ j v).mp hv
  have hClosedSA : G.IsClosedUnderValues (canonicalValue G a) s := by
    intro v hvS w hw
    have hwκ : w ∈ canonicalValue G κ v := by
      rw [← canonicalValue_frontload_eq G κ z hClosedZ v]
      exact hw
    exact hClosedS v hvS hwκ
  have hASteps :
      ∀ t : ℕ, t < n+n →
        oldStage a t = oldStage a (t+1) ∨
        G.toPredimension.IsMinimalStrongStep
          (oldStage a t) (oldStage a (t+1)) :=
    frontloadIndex_minimal_steps G κ z hClosedZ hSteps
  have hBSteps :
      ∀ t : ℕ, t < (n+n)+(n+n) →
        oldStage b t = oldStage b (t+1) ∨
        G.toPredimension.IsMinimalStrongStep
          (oldStage b t) (oldStage b (t+1)) :=
    frontloadIndex_minimal_steps G a s hClosedSA hASteps
  have hFirst : oldStage b k = s := by
    ext v
    rw [mem_oldStage_iff]
    constructor
    · intro hvLt
      by_contra hvS
      rw [frontloadIndex_outside a s v hvS] at hvLt
      by_cases hvZ : v ∈ z
      · rw [frontloadIndex_inside κ z v hvZ,
            hIndex v hvZ hvS] at hvLt
        omega
      · rw [frontloadIndex_outside κ z v hvZ] at hvLt
        omega
    · intro hvS
      rw [frontloadIndex_inside a s v hvS]
      have hBound := (a v).isLt
      omega
  have hLast : oldStage b (k+1) = z := by
    ext v
    rw [mem_oldStage_iff]
    constructor
    · intro hvLt
      by_contra hvZ
      have hvS : v ∉ s := by
        intro hvS
        exact hvZ (hsz hvS)
      rw [frontloadIndex_outside a s v hvS,
          frontloadIndex_outside κ z v hvZ] at hvLt
      omega
    · intro hvZ
      by_cases hvS : v ∈ s
      · rw [frontloadIndex_inside a s v hvS]
        have hBound := (a v).isLt
        omega
      · rw [frontloadIndex_outside a s v hvS,
            frontloadIndex_inside κ z v hvZ,
            hIndex v hvZ hvS]
        omega
  have hStep := hBSteps k (by omega)
  rcases hStep with hEq | hMin
  · rw [hFirst, hLast] at hEq
    have hxS : x ∈ s := by
      rw [hEq]
      exact hxZ
    exact (hxNotS hxS).elim
  · rw [hFirst, hLast] at hMin
    exact hMin

/-- If the complement of a finite C₀-closed set is precisely one
intrinsic component, its inclusion into the whole vertex set is
a minimal strong step. This is the special case z = univ. -/
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
  have hUnivClosed :
      G.IsClosedUnderValues (canonicalValue G κ)
        (Finset.univ : Finset V) := by
    intro _ _ v _
    exact Finset.mem_univ v
  exact closed_one_component_interval_minimal
    G κ hSteps s Finset.univ (Finset.subset_univ s)
    hClosed hUnivClosed x hComplement

end FiniteC0
end BigHrushovski
