import BigHrushovski.OrientationComponentDownsets
import Mathlib.Tactic

/-!
# Successor closure of a strongly connected component

For a finite orientation, let B be the strongly connected component
of x. The successor closure C_B of B equals the successor closure
of x, and its strict lower part P_B = C_B \ B is successor-closed.
In particular P_B is strong in C_B.

This is the actual finite lower-part geometry required by the local
stabilizer factor g_A(B) in the N₀ exact-degree formula. It does not
identify an arbitrary global orientation automorphism with an
automorphism of C_B.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The complete successor closure of the component of x. -/
noncomputable def componentClosure (x : V) : Finset V :=
  O.successorClosure (O.component x)

/-- All proper successors of the component of x. -/
noncomputable def lowerPart (x : V) : Finset V :=
  O.componentClosure x \ O.component x

theorem component_subset_componentClosure (x : V) :
    O.component x ⊆ O.componentClosure x :=
  O.subset_successorClosure (O.component x)

/-- Any vertex of a strongly connected component generates its
entire successor closure. -/
theorem componentClosure_eq_singleton (x : V) :
    O.componentClosure x =
      O.successorClosure ({x} : Finset V) := by
  apply Finset.Subset.antisymm
  · exact O.successorClosure_minimal
      (O.component_subset_successorClosure x)
      (O.successorClosure_isClosed ({x} : Finset V))
  · apply O.successorClosure_mono
    intro y hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    exact O.self_mem_component x

theorem lowerPart_subset_componentClosure (x : V) :
    O.lowerPart x ⊆ O.componentClosure x := by
  intro y hy
  exact (Finset.mem_sdiff.mp hy).1

/-- The lower part does not meet its top strongly connected component. -/
theorem lowerPart_disjoint_component (x : V) :
    Disjoint (O.lowerPart x) (O.component x) := by
  apply Finset.disjoint_left.mpr
  intro y hy hcomp
  exact (Finset.mem_sdiff.mp hy).2 hcomp

/-- The component and its lower part partition the complete
one-generated successor closure. -/
theorem component_union_lowerPart (x : V) :
    O.component x ∪ O.lowerPart x = O.componentClosure x := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_union.mp hy with hyB | hyP
    · exact O.component_subset_componentClosure x hyB
    · exact (Finset.mem_sdiff.mp hyP).1
  · intro hy
    by_cases hyB : y ∈ O.component x
    · exact Finset.mem_union.mpr (Or.inl hyB)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_sdiff.mpr ⟨hy, hyB⟩))

/-- No arrow from a proper successor of B can lead back into B,
since such an arrow would create a directed path back to x.
Consequently P_B is successor-closed. -/
theorem lowerPart_isSuccessorClosed (x : V) :
    O.IsSuccessorClosed (O.lowerPart x) := by
  intro y hy z hyz
  obtain ⟨hyC, hyNotB⟩ := Finset.mem_sdiff.mp hy
  have hySingle : y ∈ O.successorClosure ({x} : Finset V) := by
    rw [← O.componentClosure_eq_singleton x]
    exact hyC
  have hxy : O.Reaches x y :=
    (O.mem_successorClosure_singleton_iff x y).mp hySingle
  have hzC : z ∈ O.componentClosure x :=
    O.successorClosure_isClosed (O.component x) y hyC hyz
  have hzNotB : z ∉ O.component x := by
    intro hzB
    have hzx : O.Reaches z x :=
      ((O.mem_component_iff x z).mp hzB).2
    have hyx : O.Reaches y x :=
      O.reaches_trans (O.reaches_arrow hyz) hzx
    exact hyNotB ((O.mem_component_iff x y).mpr ⟨hxy, hyx⟩)
  exact Finset.mem_sdiff.mpr ⟨hzC, hzNotB⟩

/-- The lower part is a strong substructure of the complete
successor closure, for the actual graph predimension. -/
theorem lowerPart_strong_in_componentClosure (x : V) :
    O.underlying.toPredimension.IsStrong
      (O.lowerPart x) (O.componentClosure x) :=
  O.successorClosed_strong
    (O.lowerPart_subset_componentClosure x)
    (O.lowerPart_isSuccessorClosed x)

/-- The two closure pieces depend only on the component, not
on the chosen generator. -/
theorem componentClosure_eq_of_stronglyConnected
    {x y : V} (hxy : O.StronglyConnected x y) :
    O.componentClosure x = O.componentClosure y := by
  have hComp := O.component_eq_of_stronglyConnected hxy
  simp only [componentClosure, hComp]

theorem lowerPart_eq_of_stronglyConnected
    {x y : V} (hxy : O.StronglyConnected x y) :
    O.lowerPart x = O.lowerPart y := by
  have hComp := O.component_eq_of_stronglyConnected hxy
  simp only [lowerPart, componentClosure, hComp]

end FiniteOrientation
end BigHrushovski
