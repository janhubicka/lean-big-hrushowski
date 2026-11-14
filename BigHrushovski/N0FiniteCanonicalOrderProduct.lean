import BigHrushovski.N0ReachableHistoryInjective
import BigHrushovski.N0CanonicalDataCardinality
import BigHrushovski.N0UnconditionalHistoryCount
import Mathlib.Tactic

/-!
# Exact finite count of the canonical labelled SCC orders

Fix a finite orientation O.  The earlier formalization builds actual
canonical labelled vertex orders by ranking the strongly connected
components in successor-first order, choosing an internal order for
each component, and checking the complete lexicographic directed
adjacency code on each one-component successor closure.

The tagged-history proof gives a bijection between the finite set of
genuinely reachable chronological SCC-order histories and the actual
canonical SCC-order assignments for each legal ranking.  The already
proved unconditional history count then supplies the product of the
local stabilizer factors.  Summing over legal SCC rankings gives the
exact number of labelled orders in this *finite canonical family*.

This theorem is not, on its own, a statement of an infinite big
Ramsey degree: the agreement of this finite canonical family with
the paper's permitted expansions, and the infinite upper and
lower bounds, are separate proof obligations.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- For each legal component ranking, the *set* of globally
canonical component-order assignments equals the image of
the complete reachable tagged histories under their actual
labelled execution map.  Both inclusions use proved finite
inverse constructions rather than a cardinality argument. -/
theorem canonicalAssignmentsAtRanking_eq_reachableImage
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    O.canonicalAssignmentsAtRanking r =
      (BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject)).image
        O.ordersFromReverseHistory := by
  classical
  ext orders
  rw [O.mem_canonicalAssignmentsAtRanking r orders]
  constructor
  · intro hCanon
    obtain ⟨history, hReach, hEq⟩ :=
      O.canonicalAssignment_has_reachableHistory r hr orders hCanon
    exact Finset.mem_image.mpr ⟨history, hReach, hEq⟩
  · intro hMem
    obtain ⟨history, hReach, hEq⟩ := Finset.mem_image.mp hMem
    rw [← hEq]
    exact O.completeReachableTaggedHistory_isCanonical
      r hr history hReach

/-- The correspondence above is a *bijection* of finite labelled
objects, not merely a surjection: two complete reachable
histories with the same executed assignment coincide. -/
theorem canonicalAssignmentsAtRanking_card_eq_reachable
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    (O.canonicalAssignmentsAtRanking r).card =
      (BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject)).card := by
  classical
  rw [O.canonicalAssignmentsAtRanking_eq_reachableImage r hr]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hEq
  exact O.ordersFromReverseHistory_injective_on_reachable
    r ha hb hEq

/-- Reindexing the chronological stabilizer factors by the
component-ranking equivalence does not change their product. -/
theorem rankLocalFactor_product_eq_componentProduct
    (r : O.ComponentRanking) :
    (∏ i ∈ Finset.range (Fintype.card O.ComponentObject),
      O.rankLocalFactor r i) =
    ∏ B : O.ComponentObject, O.componentLocalFactor B := by
  classical
  rw [Finset.prod_range]
  have hFactors :
      (∏ i : Fin (Fintype.card O.ComponentObject),
        O.rankLocalFactor r i) =
      (∏ i : Fin (Fintype.card O.ComponentObject),
        O.componentLocalFactor (r.symm i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [rankLocalFactor, i.isLt]
  rw [hFactors]
  exact Equiv.prod_comp r.symm O.componentLocalFactor

/-- For *each* legal SCC ranking, the exact cardinality of
canonical labelled internal-component order assignments is
the product of the induced closure stabilizer factors g_A(B). -/
theorem canonicalAssignmentsAtRanking_card_product
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    (O.canonicalAssignmentsAtRanking r).card =
      ∏ B : O.ComponentObject, O.componentLocalFactor B := by
  calc
    (O.canonicalAssignmentsAtRanking r).card =
      (BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject)).card :=
      O.canonicalAssignmentsAtRanking_card_eq_reachable r hr
    _ = ∏ i ∈ Finset.range (Fintype.card O.ComponentObject),
        O.rankLocalFactor r i :=
      O.reachableTaggedHistories_card_unconditional r hr
    _ = ∏ B : O.ComponentObject, O.componentLocalFactor B :=
      O.rankLocalFactor_product_eq_componentProduct r

/-- Exact finite count for the *actual labelled canonical orders*
defined by successor-first SCC intervals and complete directed
adjacency-code minima on their induced one-component closures.

The count is ell(A) times the product of true induced pointwise
lower-part automorphism stabilizer factors.  This is still a
finite expansion-count theorem, not the big Ramsey degree
theorem for the infinite limit. -/
theorem finiteCanonicalGlobalOrderCount :
    ((O.finiteCanonicalComponentEnumerations
      (n := Fintype.card V)).image OrderBefore).card =
        O.finiteComponentTypeCount := by
  apply O.finiteCanonicalOrderCount_of_uniformRankingFibres
  intro r hr
  exact O.canonicalAssignmentsAtRanking_card_product r
    ((O.mem_linearComponentRankings r).mp hr)

end FiniteOrientation
end BigHrushovski
