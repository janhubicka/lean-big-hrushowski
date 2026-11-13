import BigHrushovski.N0StageOldPositionInvariance
import Mathlib.Tactic

/-!
# Recovering the labelled top SCC order from a complete closure order

Fix an actual strongly connected component B and let x be its chosen
generator. Restrict any complete finite enumeration of C_B to B,
retaining the original labels. This restriction is itself a genuine
enumeration of the finite subtype B, not merely an order isomorphic
to one.

If a global SCC-order assignment is updated at B with a chosen order t,
then restricting its induced enumeration of C_B to B recovers t
*exactly*. Thus the map from internal B orders to complete inherited
C_B orders is injective.

The converse, that every complete C_B enumeration with the prescribed
old positions arises from such an update, remains a separate lemma.
No canonical degree formula is claimed here.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- An actual SCC is contained in the successor closure of its
chosen generator, with no change of vertex labels. -/
theorem componentObject_subset_generatorClosure
    (B : O.ComponentObject) :
    B.val ⊆ O.componentClosure (O.componentGenerator B) := by
  intro u hu
  have hComp : u ∈ O.component (O.componentGenerator B) := by
    rw [O.componentGenerator_spec B]
    exact hu
  exact O.component_subset_componentClosure
    (O.componentGenerator B) hComp

/-- The order on the actual top component B inherited from an
arbitrary complete enumeration of the full successor closure C_B. -/
noncomputable def topOrderFromClosure
    (B : O.ComponentObject) {n : ℕ}
    (e : Fin n ≃ O.componentClosure (O.componentGenerator B)) :
    Fin (Fintype.card (↥B.val)) ≃ (↥B.val) := by
  classical
  letI : LinearOrder (↥B.val) :=
    LinearOrder.lift'
      (fun u : ↥B.val =>
        e.symm (⟨u.val,
          O.componentObject_subset_generatorClosure B u.property⟩ :
          O.componentClosure (O.componentGenerator B)))
      (by
        intro u v h
        apply Subtype.ext
        exact congrArg Subtype.val (e.symm.injective h))
  exact (Fintype.orderIsoFinOfCardEq (↥B.val) rfl).toEquiv

/-- Every pairwise comparison on B is inherited literally from
the complete closure enumeration. In particular comparisons of
nonadjacent vertices are retained. -/
theorem topOrderFromClosure_order_iff
    (B : O.ComponentObject) {n : ℕ}
    (e : Fin n ≃ O.componentClosure (O.componentGenerator B))
    (u v : ↥B.val) :
    OrderBefore (O.topOrderFromClosure B e) u v ↔
      OrderBefore e
        (⟨u.val, O.componentObject_subset_generatorClosure B u.property⟩ :
          O.componentClosure (O.componentGenerator B))
        (⟨v.val, O.componentObject_subset_generatorClosure B v.property⟩ :
          O.componentClosure (O.componentGenerator B)) := by
  classical
  letI : LinearOrder (↥B.val) :=
    LinearOrder.lift'
      (fun z : ↥B.val =>
        e.symm (⟨z.val,
          O.componentObject_subset_generatorClosure B z.property⟩ :
          O.componentClosure (O.componentGenerator B)))
      (by
        intro z w h
        apply Subtype.ext
        exact congrArg Subtype.val (e.symm.injective h))
  let E : Fin (Fintype.card (↥B.val)) ≃o (↥B.val) :=
    Fintype.orderIsoFinOfCardEq (↥B.val) rfl
  change E.symm u < E.symm v ↔
      e.symm
        (⟨u.val, O.componentObject_subset_generatorClosure B u.property⟩ :
          O.componentClosure (O.componentGenerator B)) <
      e.symm
        (⟨v.val, O.componentObject_subset_generatorClosure B v.property⟩ :
          O.componentClosure (O.componentGenerator B))
  change E.symm u < E.symm v ↔ u < v
  constructor
  · intro h
    simpa using E.strictMono h
  · intro h
    exact E.symm.strictMono h

/-- After changing the internal SCC order to t in a complete
global component-order assignment, the order inherited by C_B
restricts to exactly t on B. This is literal equality of
labelled enumerations of B. -/
theorem topOrderFromClosure_after_update
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    O.topOrderFromClosure B
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B choice))
        (O.componentGenerator B)) = choice := by
  let updated : O.ComponentLocalEnumerations :=
    O.withComponentOrder orders B choice
  let global : Fin (Fintype.card V) ≃ V :=
    O.assembleComponentEnumerations r updated
  let e := O.inheritedComponentEnumeration global (O.componentGenerator B)
  have hAt : updated B = choice :=
    O.withComponentOrder_at orders B choice
  change O.topOrderFromClosure B e = choice
  apply enumeration_eq_of_same_order
  intro u v
  calc
    OrderBefore (O.topOrderFromClosure B e) u v ↔
        OrderBefore e
          (⟨u.val,
            O.componentObject_subset_generatorClosure B u.property⟩ :
            O.componentClosure (O.componentGenerator B))
          (⟨v.val,
            O.componentObject_subset_generatorClosure B v.property⟩ :
            O.componentClosure (O.componentGenerator B)) :=
      O.topOrderFromClosure_order_iff B e u v
    _ ↔ OrderBefore global u.val v.val :=
      O.inheritedComponentEnumeration_order_iff
        global (O.componentGenerator B) _ _
    _ ↔ OrderBefore (updated B) u v :=
      O.assembleComponentEnumerations_on_component
        r updated B u v
    _ ↔ OrderBefore choice u v := by rw [hAt]

/-- Updating B with different internal orders yields different
complete enumerations of C_B, even if all other SCCs are fixed. -/
theorem inheritedClosure_injective_in_topOrder
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Function.Injective
      (fun choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val) =>
        O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B choice))
          (O.componentGenerator B)) := by
  intro a b hab
  calc
    a = O.topOrderFromClosure B
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B a))
          (O.componentGenerator B)) :=
      (O.topOrderFromClosure_after_update r orders B a).symm
    _ = O.topOrderFromClosure B
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B b))
          (O.componentGenerator B)) := by rw [hab]
    _ = b := O.topOrderFromClosure_after_update r orders B b

end FiniteOrientation
end BigHrushovski
