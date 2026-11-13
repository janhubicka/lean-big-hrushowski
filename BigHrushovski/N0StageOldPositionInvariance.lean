import BigHrushovski.N0InitialLowerPositions
import BigHrushovski.N0CanonicalStageChoices
import BigHrushovski.N0CanonicalPrefixLocality
import Mathlib.Tactic

/-!
# The old successor part is fixed when the top SCC order changes

Let B be an actual strongly connected component, C_B its complete
successor closure, and P_B = C_B \ B. Fix a legal ranking of the SCCs.
Changing the chosen enumeration of B does not change any comparison
between vertices outside B. In particular, it preserves the complete
induced order of P_B.

Since P_B is an initial segment in the inherited enumeration of C_B
for every legal SCC ranking, the previously proved finite initial-part
lemma converts equality of the old order into agreement at *every old
ordinal position*. This is the first of the two missing ingredients
in the uniform canonical next-component fibre count.

The theorems do not count component orders or assert any Ramsey degree.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Changing the internal order of B does not change any pairwise
comparison between vertices outside B. No legality assumption on
the SCC ranking is needed for this statement. -/
theorem withComponentOrder_preserves_outside_comparisons
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val))
    {u v : V} (hu : u ∉ B.val) (hv : v ∉ B.val) :
    OrderBefore
      (O.assembleComponentEnumerations r orders) u v ↔
    OrderBefore
      (O.assembleComponentEnumerations r
        (O.withComponentOrder orders B newOrder)) u v := by
  by_cases hsc : O.StronglyConnected u v
  · let C : O.ComponentObject :=
      ⟨O.component u, O.component_mem_components u⟩
    have huC : u ∈ C.val := O.self_mem_component u
    have hvC : v ∈ C.val :=
      (O.mem_component_iff u v).mpr hsc
    have hCB : C ≠ B := by
      intro hEq
      have hMem : u ∈ B.val := by
        rw [← hEq]
        exact huC
      exact hu hMem
    have hOrders :
        (O.withComponentOrder orders B newOrder) C = orders C :=
      O.withComponentOrder_other orders B C hCB newOrder
    calc
      OrderBefore (O.assembleComponentEnumerations r orders) u v ↔
          OrderBefore (orders C)
            (⟨u, huC⟩ : ↥C.val) (⟨v, hvC⟩ : ↥C.val) :=
        O.assembleComponentEnumerations_on_component r orders C
          ⟨u, huC⟩ ⟨v, hvC⟩
      _ ↔ OrderBefore ((O.withComponentOrder orders B newOrder) C)
          (⟨u, huC⟩ : ↥C.val) (⟨v, hvC⟩ : ↥C.val) := by
        rw [hOrders]
      _ ↔ OrderBefore
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B newOrder)) u v :=
        (O.assembleComponentEnumerations_on_component r
          (O.withComponentOrder orders B newOrder) C
          ⟨u, huC⟩ ⟨v, hvC⟩).symm
  · have hDiff : O.component u ≠ O.component v := by
      intro hEq
      exact hsc ((O.stronglyConnected_iff_component_eq u v).mpr hEq)
    exact (O.assembleComponentEnumerations_distinctComponents
      r orders hDiff).trans
        (O.assembleComponentEnumerations_distinctComponents
          r (O.withComponentOrder orders B newOrder) hDiff).symm

/-- With a legal component ranking, the strict lower part P_B is
an initial segment of the order inherited by C_B. It need not be
an initial segment of the whole ambient graph. -/
theorem assembledClosure_lowerPart_initial
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (x : V) :
    IsLowerBeforeRest (O.inducedLowerPart x)
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders) x) := by
  intro u v hu hv
  exact O.inheritedComponentEnumeration_lower_before_top
    (O.assembleComponentEnumerations r orders)
    (O.assembleComponentEnumerations_isSuccessorFirst r orders hr)
    x hu ((O.not_mem_inducedLowerPart_iff_mem_component x v).mp hv)

/-- When x belongs to B, no vertex of the strict lower successor
part P_B belongs to B. This uses actual SCC equality, not an
ambient undirected connectivity condition. -/
theorem lowerPart_disjoint_namedComponent
    (B : O.ComponentObject) {x u : V}
    (hx : x ∈ B.val) (hu : u ∈ O.lowerPart x) :
    u ∉ B.val := by
  have hComp : O.component x = B.val :=
    O.component_eq_of_mem_componentObject B hx
  have hNot : u ∉ O.component x := (Finset.mem_sdiff.mp hu).2
  rw [hComp] at hNot
  exact hNot

/-- The entire ordered old part P_B has unchanged comparisons
when only the enumeration of its top component B is changed.
In particular no unrelated earlier SCC enters the calculation. -/
theorem withComponentOrder_preserves_lowerPart_order
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    {x : V} (hx : x ∈ B.val)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val))
    {u v : O.componentClosure x}
    (hu : u ∈ O.inducedLowerPart x)
    (hv : v ∈ O.inducedLowerPart x) :
    OrderBefore
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders) x) u v ↔
    OrderBefore
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B newOrder)) x) u v := by
  have huP : u.val ∈ O.lowerPart x :=
    (O.mem_inducedLowerPart_iff x u).mp hu
  have hvP : v.val ∈ O.lowerPart x :=
    (O.mem_inducedLowerPart_iff x v).mp hv
  have huNotB : u.val ∉ B.val :=
    O.lowerPart_disjoint_namedComponent B hx huP
  have hvNotB : v.val ∉ B.val :=
    O.lowerPart_disjoint_namedComponent B hx hvP
  calc
    OrderBefore
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r orders) x) u v ↔
      OrderBefore (O.assembleComponentEnumerations r orders)
        u.val v.val :=
      O.inheritedComponentEnumeration_order_iff
        (O.assembleComponentEnumerations r orders) x u v
    _ ↔ OrderBefore
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B newOrder)) u.val v.val :=
      O.withComponentOrder_preserves_outside_comparisons
        r orders B newOrder huNotB hvNotB
    _ ↔ OrderBefore
        (O.inheritedComponentEnumeration
          (O.assembleComponentEnumerations r
            (O.withComponentOrder orders B newOrder)) x) u v :=
      (O.inheritedComponentEnumeration_order_iff
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B newOrder)) x u v).symm

/-- The local complete enumerations before and after changing B
have literally identical old positions on P_B. This is the
positionwise fixation required by the complete-code fibre. -/
theorem withComponentOrder_preserves_lowerPositions
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    {x : V} (hx : x ∈ B.val)
    (newOrder : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    SameLowerPositions (O.inducedLowerPart x)
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r orders) x)
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B newOrder)) x) := by
  apply sameLowerPositions_of_initial_and_oldOrder
    (O.inducedLowerPart x)
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r orders) x)
    (O.inheritedComponentEnumeration
      (O.assembleComponentEnumerations r
        (O.withComponentOrder orders B newOrder)) x)
    (O.assembledClosure_lowerPart_initial r hr orders x)
    (O.assembledClosure_lowerPart_initial r hr
      (O.withComponentOrder orders B newOrder) x)
  intro u hu v hv
  exact O.withComponentOrder_preserves_lowerPart_order
    r orders B hx newOrder hu hv

/-- Two different choices of the order on B always induce complete
C_B enumerations agreeing at all old positions. Neither choice
needs to be canonical for this assertion. -/
theorem twoComponentChoices_sameLowerPositions
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    {x : V} (hx : x ∈ B.val)
    (first second : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    SameLowerPositions (O.inducedLowerPart x)
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B first)) x)
      (O.inheritedComponentEnumeration
        (O.assembleComponentEnumerations r
          (O.withComponentOrder orders B second)) x) := by
  have hFirst :=
    O.withComponentOrder_preserves_lowerPositions r hr orders
      B hx first
  have hSecond :=
    O.withComponentOrder_preserves_lowerPositions r hr orders
      B hx second
  exact sameLowerPositions_trans (O.inducedLowerPart x)
    _ _ _
    (sameLowerPositions_symm (O.inducedLowerPart x) _ _ hFirst)
    hSecond

end FiniteOrientation
end BigHrushovski
