import BigHrushovski.OrientationComponentOrder
import Mathlib.Tactic

/-!
# Successor-closed sets are component downsets

The intrinsic description of successor-closed substructures of a finite
orientation: they are exactly the unions of whole strongly connected
components which are downward closed under the component dependency
order.  This is independent of any chosen enumeration or internal
ordering of a component.

It is the finite structural reduction used to count the possible
component orders in the N₀ big Ramsey degree formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- A successor-closed set contains the entire strongly connected
component of each of its vertices. -/
theorem successorClosed_component_subset [Fintype V]
    {s : Finset V}
    (hs : O.IsSuccessorClosed s)
    {x : V} (hx : x ∈ s) :
    O.component x ⊆ s := by
  intro y hy
  have hxy : O.Reaches x y :=
    ((O.mem_component_iff x y).mp hy).1
  exact O.successorClosed_of_reaches hs hx hxy

/-- Any strict successor of a vertex in a successor-closed set
also belongs to the set, irrespective of the chosen
representatives of their components. -/
theorem successorClosed_predecessor [Fintype V]
    {s : Finset V}
    (hs : O.IsSuccessorClosed s)
    {upper lower : V}
    (hPre : O.ComponentPrecedes
      (O.component lower) (O.component upper))
    (hUpper : upper ∈ s) :
    lower ∈ s := by
  have h : O.StrictSuccessor upper lower :=
    (O.componentPrecedes_iff_strictSuccessor upper lower).mp hPre
  exact O.successorClosed_of_reaches hs hUpper h.1

/-- The exact finite order-theoretic description of successor
closure: a set is successor-closed if and only if it contains
whole SCCs and is downward closed in the intrinsic dependency
order on the component set. -/
theorem successorClosed_iff_component_downward [Fintype V]
    (s : Finset V) :
    O.IsSuccessorClosed s ↔
      (∀ x : V, x ∈ s → O.component x ⊆ s) ∧
      (∀ upper lower : V,
        O.ComponentPrecedes
          (O.component lower) (O.component upper) →
        upper ∈ s → lower ∈ s) := by
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · intro x hx
      exact O.successorClosed_component_subset hs hx
    · intro upper lower hPre hUpper
      exact O.successorClosed_predecessor hs hPre hUpper
  · rintro ⟨hSaturated, hDown⟩
    intro x hx y hxy
    have hPath : O.Reaches x y := O.reaches_arrow hxy
    rcases O.reaches_component_eq_or_precedes hPath with hSame | hPre
    · have hyComp : y ∈ O.component x := by
        rw [hSame]
        exact O.self_mem_component y
      exact hSaturated x hx hyComp
    · exact hDown x y hPre hx

end FiniteOrientation
end BigHrushovski
