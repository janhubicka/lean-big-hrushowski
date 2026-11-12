import BigHrushovski.N0RealizeLexEnumeration
import Mathlib.Tactic

/-!
# Concatenating finite orders on the actual strongly connected components

Let r be a ranking of the actual SCCs and choose a bijective
enumeration of each SCC separately. Its inverse position map assigns
a numerical rank to every vertex. These ranks are automatically
injective inside each SCC and can be combined with r to give an
actual global vertex enumeration.

The global enumeration restricts to the *chosen order* in each SCC.
If r respects the intrinsic successor dependencies, this global
enumeration is successor-first and has whole SCCs as intervals.
This construction does not impose the canonical local code
condition on each one-component closure; that is the remaining
compatibility condition in the finite N0 expansion count.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- An enumeration of the vertices of each actual SCC, indexed
by a consecutive finite ordinal of the correct component size. -/
abbrev ComponentLocalEnumerations : Type _ :=
  ∀ B : O.ComponentObject,
    Fin (Fintype.card (↥B.val)) ≃ (↥B.val)

/-- The local rank of each vertex in its own SCC's chosen enumeration.
The same rank value may occur in different SCCs. -/
noncomputable def componentLocalRanks
    (orders : O.ComponentLocalEnumerations) (x : V) : ℕ :=
  ((orders ⟨O.component x, O.component_mem_components x⟩).symm
    ⟨x, O.self_mem_component x⟩).val

/-- Local ranks agree with the chosen local order on each component.
The proof explicitly identifies each vertex's intrinsic SCC with B. -/
theorem componentLocalRanks_lt_iff
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) (x y : ↥B.val) :
    O.componentLocalRanks orders x.val <
      O.componentLocalRanks orders y.val ↔
    OrderBefore (orders B) x y := by
  have hx : O.component x.val = B.val :=
    O.component_eq_of_mem_componentObject B x.property
  have hy : O.component y.val = B.val :=
    O.component_eq_of_mem_componentObject B y.property
  have hBx : (⟨O.component x.val, O.component_mem_components x.val⟩ :
      O.ComponentObject) = B := Subtype.ext hx
  have hBy : (⟨O.component y.val, O.component_mem_components y.val⟩ :
      O.ComponentObject) = B := Subtype.ext hy
  simp [componentLocalRanks, OrderBefore, Fin.lt_def, hBx, hBy]

/-- The local rank function is injective in each SCC, because
every component enumeration is bijective. -/
theorem componentLocalRanks_locallyInjective
    (orders : O.ComponentLocalEnumerations) :
    O.LocallyInjective (O.componentLocalRanks orders) := by
  intro x y hxy hRank
  let B : O.ComponentObject :=
    ⟨O.component x, O.component_mem_components x⟩
  have hx : x ∈ B.val := O.self_mem_component x
  have hy : y ∈ B.val :=
    (O.mem_component_iff x y).mpr hxy
  have hComp : O.component x = O.component y :=
    O.component_eq_of_stronglyConnected hxy
  have hRank' :
      ((orders B).symm ⟨x, hx⟩).val =
        ((orders B).symm ⟨y, hy⟩).val := by
    simpa only [componentLocalRanks, B, ← hComp] using hRank
  have hInv :
      (orders B).symm ⟨x, hx⟩ =
        (orders B).symm ⟨y, hy⟩ :=
    Fin.ext hRank'
  exact congrArg Subtype.val ((orders B).symm.injective hInv)

/-- Concatenate the chosen component orders using their
component ranking as the leading lexicographic key. -/
noncomputable def assembleComponentEnumerations
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    Fin (Fintype.card V) ≃ V :=
  O.lexComponentEnumeration r
    (O.componentLocalRanks orders)
    (O.componentLocalRanks_locallyInjective orders)

/-- The global enumeration has exactly the prescribed order on
each SCC, including comparisons between nonadjacent vertices. -/
theorem assembleComponentEnumerations_on_component
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) (x y : ↥B.val) :
    OrderBefore (O.assembleComponentEnumerations r orders)
        x.val y.val ↔ OrderBefore (orders B) x y := by
  have hx : O.component x.val = B.val :=
    O.component_eq_of_mem_componentObject B x.property
  have hy : O.component y.val = B.val :=
    O.component_eq_of_mem_componentObject B y.property
  have hxy : O.StronglyConnected x.val y.val :=
    (O.stronglyConnected_iff_component_eq x.val y.val).mpr
      (hx.trans hy.symm)
  calc
    OrderBefore (O.assembleComponentEnumerations r orders) x.val y.val ↔
        O.GlobalLexBefore r (O.componentLocalRanks orders)
          x.val y.val :=
      O.lexComponentEnumeration_order_iff r
        (O.componentLocalRanks orders)
        (O.componentLocalRanks_locallyInjective orders) x.val y.val
    _ ↔ O.componentLocalRanks orders x.val <
        O.componentLocalRanks orders y.val :=
      O.globalLexBefore_sameComponent_iff r
        (O.componentLocalRanks orders) hxy
    _ ↔ OrderBefore (orders B) x y :=
      O.componentLocalRanks_lt_iff orders B x y

/-- The assembled actual labelled order has whole SCCs as intervals. -/
theorem assembleComponentEnumerations_isComponentInterval
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    O.IsComponentIntervalEnumeration
      (O.assembleComponentEnumerations r orders) :=
  O.lexComponentEnumeration_isComponentInterval r
    (O.componentLocalRanks orders)
    (O.componentLocalRanks_locallyInjective orders)

/-- If r respects successor dependencies, then the assembled
enumeration is successor-first. -/
theorem assembleComponentEnumerations_isSuccessorFirst
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (hr : O.IsLinearComponentRanking r) :
    O.IsSuccessorFirstEnumeration
      (O.assembleComponentEnumerations r orders) :=
  O.lexComponentEnumeration_isSuccessorFirst r
    (O.componentLocalRanks orders)
    (O.componentLocalRanks_locallyInjective orders) hr

/-- The assembled order is an actual successor-first
component-interval enumeration whenever r is legal. -/
theorem assembleComponentEnumerations_mem_successorFirstIntervals
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (hr : O.IsLinearComponentRanking r) :
    O.assembleComponentEnumerations r orders ∈
      (O.successorFirstIntervalEnumerations
        (n := Fintype.card V)) :=
  O.lexComponentEnumeration_mem_successorFirstIntervals r
    (O.componentLocalRanks orders)
    (O.componentLocalRanks_locallyInjective orders) hr

end FiniteOrientation
end BigHrushovski
