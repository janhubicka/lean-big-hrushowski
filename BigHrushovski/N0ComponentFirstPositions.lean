import BigHrushovski.N0ComponentLinearExtensions
import Mathlib.Tactic

/-!
# Recovering the component order from a finite vertex enumeration

Every component has a unique first position in a complete
enumeration of the labelled vertices. Different components
have distinct first positions. If the enumeration puts every
proper directed successor before its source, these first
positions respect the intrinsic component dependency order.

These are structural facts about actual enumerations. No
"permitted order" is defined by a product formula here;
the remaining task is to show component intervals and
local canonical choices give a bijective reconstruction.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- An actual strongly connected component is nonempty. -/
theorem componentObject_nonempty (B : O.ComponentObject) :
    B.val.Nonempty := by
  have hB : B.val ∈ (Finset.univ : Finset V).image O.component := B.property
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hB
  refine ⟨x, ?_⟩
  rw [← hx]
  exact O.self_mem_component x

/-- Membership in a component recovers its intrinsic component set. -/
theorem component_eq_of_mem_componentObject
    (B : O.ComponentObject) {x : V} (hx : x ∈ B.val) :
    O.component x = B.val := by
  have hB : B.val ∈ (Finset.univ : Finset V).image O.component := B.property
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hB
  have hxy : O.StronglyConnected y x := by
    apply (O.mem_component_iff y x).mp
    rw [hy]
    exact hx
  exact (O.component_eq_of_stronglyConnected hxy).symm.trans hy

/-- The first occurrence of a component in a complete labelled
vertex enumeration. The minimum exists since each SCC is nonempty. -/
noncomputable def firstComponentPosition {n : ℕ}
    (e : Fin n ≃ V) (B : O.ComponentObject) : Fin n :=
  (B.val.image e.symm).min'
    (Finset.image_nonempty.mpr (O.componentObject_nonempty B))

/-- A component's first position is occupied by one of its vertices. -/
theorem firstComponentPosition_mem {n : ℕ}
    (e : Fin n ≃ V) (B : O.ComponentObject) :
    ∃ x ∈ B.val, e.symm x = O.firstComponentPosition e B := by
  have hMem : O.firstComponentPosition e B ∈ B.val.image e.symm :=
    Finset.min'_mem (B.val.image e.symm)
      (Finset.image_nonempty.mpr (O.componentObject_nonempty B))
  exact Finset.mem_image.mp hMem

theorem firstComponentPosition_le {n : ℕ}
    (e : Fin n ≃ V) (B : O.ComponentObject)
    {x : V} (hx : x ∈ B.val) :
    O.firstComponentPosition e B ≤ e.symm x := by
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Two distinct components cannot start at the same vertex
position in a bijective enumeration. -/
theorem firstComponentPosition_injective {n : ℕ}
    (e : Fin n ≃ V) :
    Function.Injective (O.firstComponentPosition e) := by
  intro B C hFirst
  obtain ⟨x, hx, hxFirst⟩ := O.firstComponentPosition_mem e B
  obtain ⟨y, hy, hyFirst⟩ := O.firstComponentPosition_mem e C
  have hxyRanks : e.symm x = e.symm y :=
    hxFirst.trans (hFirst.trans hyFirst.symm)
  have hxy : x = y := e.symm.injective hxyRanks
  subst y
  have hBx := O.component_eq_of_mem_componentObject B hx
  have hCx := O.component_eq_of_mem_componentObject C hy
  apply Subtype.ext
  exact hBx.symm.trans hCx

/-- The successor-first condition for a complete vertex
enumeration: any vertex in a proper successor component
occurs before every vertex in the component depending on it. -/
def IsSuccessorFirstEnumeration {n : ℕ}
    (e : Fin n ≃ V) : Prop :=
  ∀ x y : V, O.StrictSuccessor x y → e.symm y < e.symm x

/-- The order of component first appearances necessarily extends
the intrinsic dependency order when the vertices are successor-first.
This statement does not assume the components are intervals. -/
theorem firstComponentPosition_respectsDependencies {n : ℕ}
    (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e)
    (B C : O.ComponentObject)
    (hBC : O.ComponentPrecedes B.val C.val) :
    O.firstComponentPosition e B <
      O.firstComponentPosition e C := by
  obtain ⟨c, hc, hcFirst⟩ := O.firstComponentPosition_mem e C
  obtain ⟨b, hb, _⟩ := O.firstComponentPosition_mem e B
  have hC : O.component c = C.val :=
    O.component_eq_of_mem_componentObject C hc
  have hB : O.component b = B.val :=
    O.component_eq_of_mem_componentObject B hb
  have hStrict : O.StrictSuccessor c b := by
    apply (O.componentPrecedes_iff_strictSuccessor c b).mp
    simpa only [hB, hC] using hBC
  have hcb : e.symm b < e.symm c := he c b hStrict
  calc
    O.firstComponentPosition e B ≤ e.symm b :=
      O.firstComponentPosition_le e B hb
    _ < e.symm c := hcb
    _ = O.firstComponentPosition e C := hcFirst

end FiniteOrientation
end BigHrushovski
