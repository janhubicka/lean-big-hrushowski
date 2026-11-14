import BigHrushovski.N0TaggedHistoryCanonicalStep
import Mathlib.Tactic

/-!
# Reachable tagged histories yield canonical component assignments

Fix a legal ranking of the actual strongly connected components of
a finite orientation.  At each stage a reachable tagged history
chooses an internal labelled order of the next SCC satisfying the
complete canonical-code condition on that component's actual successor
closure.

The induction below proves that every component already processed
remains canonical: later updates cannot change the induced complete
closure enumeration of an earlier SCC.  Therefore the complete
assignment executed from any reachable history of length equal to the
number of SCCs is genuinely canonical.

This establishes one direction of the desired finite bijection.
The converse, from every canonical assignment to a reachable history,
and injectivity of the reconstruction map on reachable histories,
remain separate proof obligations.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Every SCC appearing among the first n ranked components has
a canonical induced complete closure order after executing any
reachable history of n tagged next-component choices. -/
theorem reachableTaggedHistory_canonical_prior
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r) :
    ∀ (n : ℕ) (history : List O.TaggedComponentOrder),
      history ∈
        BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r) n →
      ∀ C : O.ComponentObject, (r C).val < n →
        O.IsCanonicalAtComponent r
          (O.ordersFromReverseHistory history) C := by
  intro n
  induction n with
  | zero =>
      intro history hReach C hRank
      omega
  | succ n ih =>
      intro history hReach C hRank
      change history ∈
        (BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r) n).biUnion
          (fun prior => (O.canonicalTaggedNextChoices r prior).image
            (fun tag => tag :: prior)) at hReach
      obtain ⟨prior, hPrior, hImage⟩ := Finset.mem_biUnion.mp hReach
      obtain ⟨tag, hTag, hList⟩ := Finset.mem_image.mp hImage
      subst history
      have hLen : prior.length = n :=
        BigHrushovski.FiniteChoiceHistory.length_of_mem_reachableHistories
          (O.canonicalTaggedNextChoices r) n prior hPrior
      by_cases hBound : prior.length < Fintype.card O.ComponentObject
      · obtain ⟨choice, hTagEq, hCanon⟩ :=
          (O.mem_canonicalTaggedNextChoices_iff r prior hBound tag).mp hTag
        subst tag
        let B : O.ComponentObject :=
          r.symm ⟨prior.length, hBound⟩
        have hRankB : (r B).val = n := by
          simp [B, hLen]
        have hExecute :
            O.ordersFromReverseHistory
              ((⟨B, choice⟩ : O.TaggedComponentOrder) :: prior) =
            O.withComponentOrder
              (O.ordersFromReverseHistory prior) B choice :=
          O.ordersFromReverseHistory_cons
            (⟨B, choice⟩ : O.TaggedComponentOrder) prior
        rw [hExecute]
        by_cases hCB : C = B
        · subst C
          exact hCanon
        · have hRankNe : (r C).val ≠ n := by
            intro heq
            apply hCB
            apply r.injective
            apply Fin.ext
            omega
          have hEarlier : (r C).val < n := by omega
          have hBefore : r C < r B := by
            change (r C).val < (r B).val
            omega
          exact (O.canonicalAtComponent_iff_later_update
            r hr (O.ordersFromReverseHistory prior)
            C B hBefore choice).mp
              (ih prior hPrior C hEarlier)
      · simp [canonicalTaggedNextChoices, hBound] at hTag

/-- A complete reachable tagged history produces an actual family
of SCC orders passing the original all-generator canonical test
at every component.  No quotient by automorphisms is used. -/
theorem completeReachableTaggedHistory_isCanonical
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (history : List O.TaggedComponentOrder)
    (hReach :
      history ∈ BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject)) :
    O.IsCanonicalComponentAssignment r
      (O.ordersFromReverseHistory history) := by
  apply (O.isCanonicalComponentAssignment_iff_forall_component r
    (O.ordersFromReverseHistory history)).mpr
  intro C
  exact O.reachableTaggedHistory_canonical_prior r hr
    (Fintype.card O.ComponentObject) history hReach C (r C).isLt

end FiniteOrientation
end BigHrushovski
