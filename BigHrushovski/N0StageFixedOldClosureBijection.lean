import BigHrushovski.N0StageTopOrderRestriction
import Mathlib.Tactic

/-!
# Every fixed-old closure enumeration comes from a top-SCC order

Fix a legal ranking of the actual SCCs and a complete family of
component orders. For an actual component B, let C_B be its complete
successor closure and P_B=C_B\B.

Changing only B changes no old position in the inherited C_B
enumeration (the previous module). Conversely, any complete
enumeration of C_B agreeing at those old positions is obtained
uniquely by updating B to its induced labelled top order. The proof
compares all labelled pairs in the lower part, in the top SCC,
and between the two parts; no appeal to a graph automorphism is made.

Thus the fixed-old enumeration family is exactly the image of all
possible internal B orders under the genuine SCC assembly map.
This is the geometric bijection needed for the canonical fibre count.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- The complete actual enumeration of C_B inherited from the
current SCC-order assignment, before changing B. -/
noncomputable def stageBaseClosureEnumeration
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Fin (Fintype.card
      (↥(O.componentClosure (O.componentGenerator B)))) ≃
        O.componentClosure (O.componentGenerator B) :=
  O.inheritedComponentEnumeration
    (O.assembleComponentEnumerations r orders)
    (O.componentGenerator B)

/-- The complete enumeration of C_B produced by replacing the
internal order of B by a proposed new labelled order. -/
noncomputable def stageClosureFromTop
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    Fin (Fintype.card
      (↥(O.componentClosure (O.componentGenerator B)))) ≃
        O.componentClosure (O.componentGenerator B) :=
  O.inheritedComponentEnumeration
    (O.assembleComponentEnumerations r
      (O.withComponentOrder orders B choice))
    (O.componentGenerator B)

/-- Every actual proposed top order yields a complete closure
enumeration fixing the same old positions as the baseline. -/
theorem stageClosureFromTop_fixedLower
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    SameLowerPositions (O.inducedLowerPart (O.componentGenerator B))
      (O.stageBaseClosureEnumeration r orders B)
      (O.stageClosureFromTop r orders B choice) := by
  have hxB : O.componentGenerator B ∈ B.val := by
    rw [← O.componentGenerator_spec B]
    exact O.self_mem_component (O.componentGenerator B)
  exact O.withComponentOrder_preserves_lowerPositions
    r hr orders B hxB choice

/-- The labelled top order extracted from the complete closure
enumeration obtained after an update is literally the order chosen
for B. -/
theorem topOrderFromStageClosure
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    O.topOrderFromClosure B
      (O.stageClosureFromTop r orders B choice) = choice :=
  O.topOrderFromClosure_after_update r orders B choice

/-- On a complete actual C_B carrier, equality of the induced
labelled top-B orders gives equality of the full comparison
relations restricted to the complement of P_B. -/
theorem remainingOrder_eq_of_same_topOrder
    (B : O.ComponentObject) {n : ℕ}
    (e f : Fin n ≃ O.componentClosure (O.componentGenerator B))
    (hTop : O.topOrderFromClosure B e =
      O.topOrderFromClosure B f) :
    RemainingOrder (O.inducedLowerPart (O.componentGenerator B)) e =
      RemainingOrder (O.inducedLowerPart (O.componentGenerator B)) f := by
  classical
  let x : V := O.componentGenerator B
  let P : Finset (O.componentClosure x) := O.inducedLowerPart x
  funext u v
  apply propext
  have huComponent : u.val.val ∈ O.component x :=
    (O.not_mem_inducedLowerPart_iff_mem_component x u.val).mp u.property
  have hvComponent : v.val.val ∈ O.component x :=
    (O.not_mem_inducedLowerPart_iff_mem_component x v.val).mp v.property
  have huB : u.val.val ∈ B.val := by
    rw [← O.componentGenerator_spec B]
    exact huComponent
  have hvB : v.val.val ∈ B.val := by
    rw [← O.componentGenerator_spec B]
    exact hvComponent
  let bu : ↥B.val := ⟨u.val.val, huB⟩
  let bv : ↥B.val := ⟨v.val.val, hvB⟩
  have huEq :
      (⟨bu.val,
        O.componentObject_subset_generatorClosure B bu.property⟩ :
        O.componentClosure x) = u.val := Subtype.ext rfl
  have hvEq :
      (⟨bv.val,
        O.componentObject_subset_generatorClosure B bv.property⟩ :
        O.componentClosure x) = v.val := Subtype.ext rfl
  calc
    RemainingOrder P e u v ↔
        OrderBefore (O.topOrderFromClosure B e) bu bv := by
      change OrderBefore e u.val v.val ↔
        OrderBefore (O.topOrderFromClosure B e) bu bv
      rw [← huEq, ← hvEq]
      exact (O.topOrderFromClosure_order_iff B e bu bv).symm
    _ ↔ OrderBefore (O.topOrderFromClosure B f) bu bv := by
      rw [hTop]
    _ ↔ RemainingOrder P f u v := by
      change OrderBefore (O.topOrderFromClosure B f) bu bv ↔
        OrderBefore f u.val v.val
      rw [← huEq, ← hvEq]
      exact O.topOrderFromClosure_order_iff B f bu bv

/-- **Surjectivity.** Let f be any complete C_B enumeration
agreeing with the original induced enumeration at all positions
of P_B. If B is reordered by the top order inherited from f,
then the new complete induced enumeration of C_B is *exactly f*.

This does not assume that f is canonical. -/
theorem stageClosureFromTop_surjective_fixedLower
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (f : Fin (Fintype.card
        (↥(O.componentClosure (O.componentGenerator B)))) ≃
      O.componentClosure (O.componentGenerator B))
    (hf : SameLowerPositions
      (O.inducedLowerPart (O.componentGenerator B))
      (O.stageBaseClosureEnumeration r orders B) f) :
    O.stageClosureFromTop r orders B
      (O.topOrderFromClosure B f) = f := by
  let x : V := O.componentGenerator B
  let P : Finset (O.componentClosure x) := O.inducedLowerPart x
  let choice := O.topOrderFromClosure B f
  let base := O.stageBaseClosureEnumeration r orders B
  let updated := O.stageClosureFromTop r orders B choice
  have hOldUpdated : SameLowerPositions P base updated :=
    O.stageClosureFromTop_fixedLower r hr orders B choice
  have hBaseInitial : IsLowerBeforeRest P base :=
    O.assembledClosure_lowerPart_initial r hr orders x
  have hUpdatedInitial : IsLowerBeforeRest P updated :=
    O.assembledClosure_lowerPart_initial r hr
      (O.withComponentOrder orders B choice) x
  have hfInitial : IsLowerBeforeRest P f :=
    lowerBeforeRest_of_sameLowerPositions P base f hBaseInitial hf
  have hTop :
      O.topOrderFromClosure B updated = O.topOrderFromClosure B f :=
    O.topOrderFromStageClosure r orders B choice
  have hRemaining : RemainingOrder P updated = RemainingOrder P f :=
    O.remainingOrder_eq_of_same_topOrder B updated f hTop
  exact enumeration_eq_of_fixed_old_and_same_remaining_order
    P base updated f hOldUpdated hf hUpdatedInitial hfInitial hRemaining

/-- The **entire** finite fixed-old-position enumeration family of
the actual C_B is the image of *all* possible labelled internal
orders of B under the genuine component assembly construction.

This strengthens the earlier local counting of canonical order
classes: no permitted fixed-old local enumeration is omitted. -/
theorem fixedLowerEnumerations_eq_stageClosureImage
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    fixedLowerEnumerations
      (O.inducedLowerPart (O.componentGenerator B))
      (O.stageBaseClosureEnumeration r orders B) =
    (Finset.univ :
      Finset (Fin (Fintype.card (↥B.val)) ≃ (↥B.val))).image
        (O.stageClosureFromTop r orders B) := by
  classical
  ext f
  rw [mem_fixedLowerEnumerations_iff]
  constructor
  · intro hf
    apply Finset.mem_image.mpr
    refine ⟨O.topOrderFromClosure B f, Finset.mem_univ _, ?_⟩
    exact O.stageClosureFromTop_surjective_fixedLower
      r hr orders B f hf
  · intro hf
    obtain ⟨choice, _, hEq⟩ := Finset.mem_image.mp hf
    rw [← hEq]
    exact O.stageClosureFromTop_fixedLower r hr orders B choice

/-- The fixed-old closure construction is injective in the
chosen labelled order of B, independently of the legality
assumption. -/
theorem stageClosureFromTop_injective
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject) :
    Function.Injective (O.stageClosureFromTop r orders B) :=
  O.inheritedClosure_injective_in_topOrder r orders B

end FiniteOrientation
end BigHrushovski
