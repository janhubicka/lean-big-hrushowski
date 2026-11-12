import BigHrushovski.N0CanonicalAssembly
import Mathlib.Tactic

/-!
# Recovering the full finite SCC-order data from its assembly

The component-concatenation construction is injective, not merely
surjective onto component-interval orders. An assembled labelled
enumeration recovers both its actual consecutive SCC ranking
and the chosen enumeration of *every* SCC.

This is the finite geometric bijection. The additional
canonical-code condition remains a restriction on these data,
and its number of admissible choices must still be counted.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Restriction of an assembled global order to an actual SCC is
exactly its originally selected enumeration, not just an order
isomorphic to it. -/
theorem componentOrdersFromAssembly_eq
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    O.componentOrdersFromEnumeration
      (O.assembleComponentEnumerations r orders) = orders := by
  funext B
  apply enumeration_eq_of_same_order
  intro x y
  calc
    OrderBefore
        (O.componentOrdersFromEnumeration
          (O.assembleComponentEnumerations r orders) B) x y ↔
      OrderBefore (O.assembleComponentEnumerations r orders)
        x.val y.val :=
      inducedEnumerationOn_order_iff
        (O.assembleComponentEnumerations r orders) B.val x y
    _ ↔ OrderBefore (orders B) x y :=
      O.assembleComponentEnumerations_on_component r orders B x y

/-- Ranking the SCCs by their first occurrence in an assembled
global order recovers exactly the ranking used to construct it.
The consecutive finite ranks cannot be changed without changing
some labelled intercomponent comparison. -/
theorem rankingFromAssembly_eq
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    O.rankingFromEnumeration
      (O.assembleComponentEnumerations r orders) = r := by
  classical
  let e : Fin (Fintype.card V) ≃ V :=
    O.assembleComponentEnumerations r orders
  let re : O.ComponentRanking := O.rankingFromEnumeration e
  have hCompare : ∀ B C : O.ComponentObject,
      r B < r C ↔ re B < re C := by
    intro B C
    by_cases hBC : B = C
    · subst C
      simp
    · obtain ⟨b, hb⟩ := O.componentObject_nonempty B
      obtain ⟨c, hc⟩ := O.componentObject_nonempty C
      have hbComp : O.component b = B.val :=
        O.component_eq_of_mem_componentObject B hb
      have hcComp : O.component c = C.val :=
        O.component_eq_of_mem_componentObject C hc
      have hbObject :
          (⟨O.component b, O.component_mem_components b⟩ :
            O.ComponentObject) = B := Subtype.ext hbComp
      have hcObject :
          (⟨O.component c, O.component_mem_components c⟩ :
            O.ComponentObject) = C := Subtype.ext hcComp
      have hDiff : O.component b ≠ O.component c := by
        intro h
        apply hBC
        apply Subtype.ext
        exact hbComp.symm.trans (h.trans hcComp)
      calc
        r B < r C ↔
          r ⟨O.component b, O.component_mem_components b⟩ <
            r ⟨O.component c, O.component_mem_components c⟩ := by
          simp only [hbObject, hcObject]
        _ ↔ OrderBefore e b c :=
          (O.assembleComponentEnumerations_distinctComponents
            r orders hDiff).symm
        _ ↔ O.firstComponentPosition e B <
            O.firstComponentPosition e C :=
          O.vertices_before_iff_component_first_before e
            (O.assembleComponentEnumerations_isComponentInterval r orders)
            B C hBC hb hc
        _ ↔ re B < re C :=
          (O.rankingFromEnumeration_lt_iff_firstPosition e B C).symm
  have hSymm : r.symm = re.symm := by
    apply enumeration_eq_of_same_order
    intro B C
    change r B < r C ↔ re B < re C
    exact hCompare B C
  exact (congrArg Equiv.symm hSymm).symm

/-- The full assembly map is injective on the fixed labelled vertex
set: neither SCC rankings nor their internal enumerations can
collapse to the same global enumerated order. -/
theorem assembleComponentEnumerations_injective :
    Function.Injective
      (fun data : O.ComponentRanking × O.ComponentLocalEnumerations =>
        O.assembleComponentEnumerations data.1 data.2) := by
  intro a b h
  rcases a with ⟨r₁, orders₁⟩
  rcases b with ⟨r₂, orders₂⟩
  have hr : r₁ = r₂ := by
    calc
      r₁ = O.rankingFromEnumeration
          (O.assembleComponentEnumerations r₁ orders₁) :=
        (O.rankingFromAssembly_eq r₁ orders₁).symm
      _ = O.rankingFromEnumeration
          (O.assembleComponentEnumerations r₂ orders₂) := by rw [h]
      _ = r₂ := O.rankingFromAssembly_eq r₂ orders₂
  have ho : orders₁ = orders₂ := by
    calc
      orders₁ = O.componentOrdersFromEnumeration
          (O.assembleComponentEnumerations r₁ orders₁) :=
        (O.componentOrdersFromAssembly_eq r₁ orders₁).symm
      _ = O.componentOrdersFromEnumeration
          (O.assembleComponentEnumerations r₂ orders₂) := by rw [h]
      _ = orders₂ := O.componentOrdersFromAssembly_eq r₂ orders₂
  cases hr
  cases ho
  rfl

end FiniteOrientation
end BigHrushovski
