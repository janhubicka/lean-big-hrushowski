import BigHrushovski.N0TaggedHistoryInverse
import BigHrushovski.N0CanonicalPrefixLocality
import Mathlib.Tactic

/-!
# Canonicality of earlier SCCs survives later component-order updates

Fix a legal ranking of the actual strongly connected components.
When the order of a component B is changed, no canonical complete-code
test for a component C appearing strictly earlier in that ranking
can change.  The reason is not that their lower parts are independent:
rather, the successor closure of C is contained in the rank prefix
through C, and therefore does not contain B.

We also unpack a member of the actual tagged next-choice set as the
correct SCC tag together with a choice satisfying that SCC's full
canonicality predicate.

These are the two local facts needed for an induction from reachable
tagged histories to genuinely canonical full SCC assignments.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- A later component update preserves the complete canonical
predicate for every earlier component, including comparisons of
nonedges in its genuine successor closure. -/
theorem canonicalAtComponent_iff_later_update
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (C B : O.ComponentObject)
    (hCB : r C < r B)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val)) :
    O.IsCanonicalAtComponent r orders C ↔
      O.IsCanonicalAtComponent r
        (O.withComponentOrder orders B choice) C := by
  have hAgree (x : V) (hx : x ∈ C.val) :
      O.AgreeThroughComponentRank r orders
        (O.withComponentOrder orders B choice)
        (r ⟨O.component x, O.component_mem_components x⟩) := by
    intro D hD
    have hXC :
        (⟨O.component x, O.component_mem_components x⟩ :
          O.ComponentObject) = C :=
      Subtype.ext (O.component_eq_of_mem_componentObject C hx)
    rw [hXC] at hD
    have hDB : D ≠ B := by
      intro heq
      subst D
      exact (not_le_of_gt hCB) hD
    exact (O.withComponentOrder_other orders B D hDB choice).symm
  constructor
  · intro h x hx
    exact (O.canonicalCondition_eq_of_rankPrefixAgreement r hr
      orders (O.withComponentOrder orders B choice)
      x (hAgree x hx)).mp (h x hx)
  · intro h x hx
    exact (O.canonicalCondition_eq_of_rankPrefixAgreement r hr
      orders (O.withComponentOrder orders B choice)
      x (hAgree x hx)).mpr (h x hx)

/-- A tagged next-choice member has exactly the component in the
rank position given by the history length.  Its internal order
satisfies the original all-generator complete-code condition. -/
theorem mem_canonicalTaggedNextChoices_iff
    (r : O.ComponentRanking)
    (history : List O.TaggedComponentOrder)
    (hBound : history.length < Fintype.card O.ComponentObject)
    (tag : O.TaggedComponentOrder) :
    tag ∈ O.canonicalTaggedNextChoices r history ↔
      ∃ choice :
          Fin (Fintype.card
            (↥((r.symm ⟨history.length, hBound⟩).val))) ≃
            (↥((r.symm ⟨history.length, hBound⟩).val)),
        tag = ⟨r.symm ⟨history.length, hBound⟩, choice⟩ ∧
        O.IsCanonicalAtComponent r
          (O.withComponentOrder
            (O.ordersFromReverseHistory history)
            (r.symm ⟨history.length, hBound⟩) choice)
          (r.symm ⟨history.length, hBound⟩) := by
  classical
  let B : O.ComponentObject := r.symm ⟨history.length, hBound⟩
  simp only [canonicalTaggedNextChoices, dif_pos hBound]
  constructor
  · intro h
    obtain ⟨choice, hChoice, hEq⟩ := Finset.mem_image.mp h
    exact ⟨choice, hEq.symm,
      (O.mem_canonicalNextComponentChoices r
        (O.ordersFromReverseHistory history) B choice).mp hChoice⟩
  · rintro ⟨choice, hEq, hCanon⟩
    apply Finset.mem_image.mpr
    exact ⟨choice,
      (O.mem_canonicalNextComponentChoices r
        (O.ordersFromReverseHistory history) B choice).mpr hCanon,
      hEq.symm⟩

end FiniteOrientation
end BigHrushovski
