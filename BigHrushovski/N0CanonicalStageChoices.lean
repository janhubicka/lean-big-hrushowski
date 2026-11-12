import BigHrushovski.N0AssemblyDataInverse
import BigHrushovski.N0CanonicalTopOrderFibres
import Mathlib.Tactic

/-!
# Actual one-component extension fibres in a finite SCC order

A component-order assignment is a family of bijective enumerations of
the actual strongly connected components. To extend a partial order
history at component B, we change only the enumeration of B, leaving
every other component enumeration unchanged.

The local admissibility test is the complete directed adjacency-code
condition on C_B, the real successor closure of B. We make the set of
admissible next-component enumerations a concrete finite set, and prove
that the corresponding updated *whole assignments* have exactly the
same cardinality.

The essential further step is to prove this cardinality equals
g_A(B) for each reachable earlier history. This module does not
assume or assert that step or the global degree formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- A fixed arbitrary finite enumeration for each SCC, used only
to fill components not yet reached by a chronological construction. -/
noncomputable def defaultComponentOrders :
    O.ComponentLocalEnumerations :=
  fun B => (Fintype.equivFin (↥B.val)).symm

/-- Replace the internal order of one actual SCC. Every other
component keeps its own enumeration. -/
noncomputable def withComponentOrder
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    O.ComponentLocalEnumerations := by
  classical
  exact Function.update orders B newOrder

theorem withComponentOrder_at
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    (O.withComponentOrder orders B newOrder) B = newOrder := by
  classical
  simp [withComponentOrder]

theorem withComponentOrder_other
    (orders : O.ComponentLocalEnumerations)
    (B C : O.ComponentObject) (hCB : C ≠ B)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    (O.withComponentOrder orders B newOrder) C = orders C := by
  classical
  simp [withComponentOrder, hCB]

/-- Two different choices for B give two different whole labelled
component-order assignments, regardless of the other components. -/
theorem withComponentOrder_injective
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Function.Injective
      (fun newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val) =>
        O.withComponentOrder orders B newOrder) := by
  intro a b hab
  have hB := congrArg
    (fun o : O.ComponentLocalEnumerations => o B) hab
  simpa only [O.withComponentOrder_at] using hB

/-- The concrete canonical-code predicate at an actual SCC B.
Every vertex generating that SCC is checked on its full
induced successor closure C_B, with both arrows and nonarrows. -/
def IsCanonicalAtComponent
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) : Prop :=
  ∀ x : V, x ∈ B.val →
    (let e := O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders) x;
     e ∈ O.canonicalComponentLexClass x e)

/-- The global finite canonical predicate is exactly the
conjunction of the predicates at all actual SCCs. -/
theorem isCanonicalComponentAssignment_iff_forall_component
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    O.IsCanonicalComponentAssignment r orders ↔
      ∀ B : O.ComponentObject,
        O.IsCanonicalAtComponent r orders B := by
  constructor
  · intro h B x hx
    exact h x
  · intro h x
    exact h ⟨O.component x, O.component_mem_components x⟩
      x (O.self_mem_component x)

/-- Actual permitted next internal orders of B, with every other
component fixed at its current enumeration. The finite cardinality
has not yet been identified with the stabilizer factor. -/
noncomputable def canonicalNextComponentChoices
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Finset (Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) := by
  classical
  exact Finset.univ.filter (fun newOrder =>
    O.IsCanonicalAtComponent r
      (O.withComponentOrder orders B newOrder) B)

theorem mem_canonicalNextComponentChoices
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    newOrder ∈ O.canonicalNextComponentChoices r orders B ↔
      O.IsCanonicalAtComponent r
        (O.withComponentOrder orders B newOrder) B := by
  classical
  simp [canonicalNextComponentChoices]

/-- Whole assignment records for the next legal B-choice. They
are not numerical placeholders: each record replaces exactly one
enumeration on an actual labelled SCC. -/
noncomputable def canonicalNextComponentAssignments
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Finset O.ComponentLocalEnumerations := by
  classical
  exact (O.canonicalNextComponentChoices r orders B).image
    (O.withComponentOrder orders B)

/-- Counting updated whole assignments is identical to counting
the actual permitted internal orders of B. In particular there
are no collisions from different component choices. -/
theorem canonicalNextComponentAssignments_card
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    (O.canonicalNextComponentAssignments r orders B).card =
      (O.canonicalNextComponentChoices r orders B).card := by
  classical
  unfold canonicalNextComponentAssignments
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  exact O.withComponentOrder_injective orders B hab

end FiniteOrientation
end BigHrushovski
