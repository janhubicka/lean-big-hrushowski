import BigHrushovski.N0AssembleComponentOrders
import Mathlib.Tactic

/-!
# Locality of component-closure orders under finite SCC concatenation

Fix a ranking of the actual strongly connected components and
enumerate each component independently. The resulting global
enumeration induces a complete order on every successor closure
C_B. That induced order depends only on the enumerations of
components *inside* C_B, not on the orderings chosen for unrelated
components elsewhere in the graph.

This observation is important for dependent counting of canonical
local orders. It makes no claim that the independent component
orders already satisfy the canonical adjacency-code condition.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Comparisons of vertices in distinct SCCs depend only on the
component ranking. The local enumerations play no role. -/
theorem assembleComponentEnumerations_distinctComponents
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    {u v : V} (huv : O.component u ≠ O.component v) :
    OrderBefore (O.assembleComponentEnumerations r orders) u v ↔
      r ⟨O.component u, O.component_mem_components u⟩ <
        r ⟨O.component v, O.component_mem_components v⟩ := by
  calc
    OrderBefore (O.assembleComponentEnumerations r orders) u v ↔
        O.GlobalLexBefore r (O.componentLocalRanks orders) u v :=
      O.lexComponentEnumeration_order_iff r
        (O.componentLocalRanks orders)
        (O.componentLocalRanks_locallyInjective orders) u v
    _ ↔ (O.vertexLexKey r (O.componentLocalRanks orders) u).1 <
          (O.vertexLexKey r (O.componentLocalRanks orders) v).1 :=
      O.globalLexBefore_distinctComponents_iff r
        (O.componentLocalRanks orders) huv
    _ ↔ r ⟨O.component u, O.component_mem_components u⟩ <
          r ⟨O.component v, O.component_mem_components v⟩ := by
      simp only [vertexLexKey, Fin.lt_def]

/-- If two families of internal component orders agree on every
component lying in the complete successor closure C_B, then
their assembled global orders induce exactly the same
enumeration on C_B. The ranking of components is held fixed,
but it need not be a legal successor-first ranking here. -/
theorem inheritedComponentEnumeration_eq_of_component_agreement
    (r : O.ComponentRanking)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (x : V)
    (hAgree : ∀ B : O.ComponentObject,
      B.val ⊆ O.componentClosure x →
        orders₁ B = orders₂ B) :
    O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₁) x =
      O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₂) x := by
  change inducedEnumerationOn
      (O.assembleComponentEnumerations r orders₁)
      (O.componentClosure x) =
    inducedEnumerationOn
      (O.assembleComponentEnumerations r orders₂)
      (O.componentClosure x)
  apply inducedEnumerationOn_eq_of_order_agree
  intro u hu v hv
  by_cases hsc : O.StronglyConnected u v
  · let B : O.ComponentObject :=
      ⟨O.component u, O.component_mem_components u⟩
    have huB : u ∈ B.val := O.self_mem_component u
    have hvB : v ∈ B.val :=
      (O.mem_component_iff u v).mpr hsc
    have hSub : B.val ⊆ O.componentClosure x :=
      O.successorClosed_component_subset
        (O.componentClosure_isSuccessorClosed x) hu
    have hOrders : orders₁ B = orders₂ B :=
      hAgree B hSub
    calc
      OrderBefore (O.assembleComponentEnumerations r orders₁) u v ↔
          OrderBefore (orders₁ B)
            (⟨u, huB⟩ : ↥B.val) (⟨v, hvB⟩ : ↥B.val) :=
        O.assembleComponentEnumerations_on_component r orders₁
          B ⟨u, huB⟩ ⟨v, hvB⟩
      _ ↔ OrderBefore (orders₂ B)
            (⟨u, huB⟩ : ↥B.val) (⟨v, hvB⟩ : ↥B.val) := by
        rw [hOrders]
      _ ↔ OrderBefore (O.assembleComponentEnumerations r orders₂)
          u v :=
        (O.assembleComponentEnumerations_on_component r orders₂
          B ⟨u, huB⟩ ⟨v, hvB⟩).symm
  · have hDiff : O.component u ≠ O.component v := by
      intro hEq
      exact hsc ((O.stronglyConnected_iff_component_eq u v).mpr hEq)
    exact (O.assembleComponentEnumerations_distinctComponents
      r orders₁ hDiff).trans
      (O.assembleComponentEnumerations_distinctComponents
        r orders₂ hDiff).symm

/-- The canonical-code condition at the component containing x
is likewise unaffected by changing internal orders on
components outside C_B. This is the locality needed for
successive choices in the finite counting argument. -/
theorem localCanonicalCondition_eq_of_component_agreement
    (r : O.ComponentRanking)
    (orders₁ orders₂ : O.ComponentLocalEnumerations)
    (x : V)
    (hAgree : ∀ B : O.ComponentObject,
      B.val ⊆ O.componentClosure x →
        orders₁ B = orders₂ B) :
    (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₁) x
      e ∈ O.canonicalComponentLexClass x e) ↔
    (let e := O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders₂) x
      e ∈ O.canonicalComponentLexClass x e) := by
  have h := O.inheritedComponentEnumeration_eq_of_component_agreement
    r orders₁ orders₂ x hAgree
  change
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders₁) x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r orders₁) x)) ↔
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders₂) x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r orders₂) x))
  rw [h]

end FiniteOrientation
end BigHrushovski
