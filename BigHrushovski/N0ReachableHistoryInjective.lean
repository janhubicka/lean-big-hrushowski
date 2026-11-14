import BigHrushovski.N0CanonicalAssignmentReachable
import Mathlib.Tactic

/-!
# Injectivity of the actual SCC-history reconstruction

An accepted tagged history of length n contains exactly one order
choice for each of the first n components of the chosen ranking.
Later updates never overwrite an earlier ranked component.

Consequently the partial history can be recovered from the family
of component orders obtained by executing it: read the orders of
the first n components in the prescribed ranking, newest first.

At the full length this proves injectivity on *reachable histories*.
Combined with the canonicality and surjectivity statements in the
preceding modules, it gives the missing finite history-to-assignment
bijection.  The degree count is stated separately.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Two complete assignments agreeing at all components in a rank
prefix have exactly the same tagged history for that prefix.
This is literal equality of labels and internal enumerations. -/
theorem taggedPrefixFromAssignment_eq_of_agree
    (r : O.ComponentRanking)
    (orders₁ orders₂ : O.ComponentLocalEnumerations) :
    ∀ n (hn : n ≤ Fintype.card O.ComponentObject),
      (∀ B : O.ComponentObject,
        (r B).val < n → orders₁ B = orders₂ B) →
      O.taggedPrefixFromAssignment r orders₁ n hn =
        O.taggedPrefixFromAssignment r orders₂ n hn := by
  intro n
  induction n with
  | zero =>
      intro hn hAgree
      rfl
  | succ n ih =>
      intro hn hAgree
      let B : O.ComponentObject :=
        r.symm ⟨n, Nat.lt_of_succ_le hn⟩
      have hRankB : (r B).val = n := by
        simp [B]
      have hHead : orders₁ B = orders₂ B :=
        hAgree B (by omega)
      have hTail :=
        ih (Nat.le_of_succ_le hn) (by
          intro C hC
          exact hAgree C (by omega))
      simp [taggedPrefixFromAssignment, hHead, hTail]

/-- For a reachable history, changing the order of the newly
ranked SCC never changes any of the already chosen component
orders.  The statement is independent of canonicality of those
earlier component choices. -/
theorem withNewRankOrder_preserves_earlier
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations)
    (B : O.ComponentObject)
    (choice : Fin (Fintype.card (↥B.val)) ≃ (↥B.val))
    (n : ℕ)
    (hRankB : (r B).val = n)
    (C : O.ComponentObject)
    (hEarlier : (r C).val < n) :
    (O.withComponentOrder orders B choice) C = orders C := by
  have hCB : C ≠ B := by
    intro heq
    subst C
    omega
  exact O.withComponentOrder_other orders B C hCB choice

/-- A genuine reachable history of length n is *exactly* the
tagged rank-prefix history read from its executed component-order
assignment.  This supplies the inverse map on reachable histories. -/
theorem taggedPrefix_of_reachableHistory
    (r : O.ComponentRanking) :
    ∀ n (hn : n ≤ Fintype.card O.ComponentObject)
      (history : List O.TaggedComponentOrder),
      history ∈
        BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r) n →
      O.taggedPrefixFromAssignment r
        (O.ordersFromReverseHistory history) n hn = history := by
  intro n
  induction n with
  | zero =>
      intro hn history hReach
      have hNil : history = [] := by
        simpa [BigHrushovski.FiniteChoiceHistory.reachableHistories]
          using hReach
      subst history
      rfl
  | succ n ih =>
      intro hn history hReach
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
        let updated : O.ComponentLocalEnumerations :=
          O.withComponentOrder
            (O.ordersFromReverseHistory prior) B choice
        have hRankB : (r B).val = n := by
          simp [B, hLen]
        have hState :
            O.ordersFromReverseHistory
              ((⟨B, choice⟩ : O.TaggedComponentOrder) :: prior) =
                updated :=
          O.ordersFromReverseHistory_cons
            (⟨B, choice⟩ : O.TaggedComponentOrder) prior
        have hAtB : updated B = choice :=
          O.withComponentOrder_at
            (O.ordersFromReverseHistory prior) B choice
        have hEarlier :
            ∀ C : O.ComponentObject, (r C).val < n →
              updated C = (O.ordersFromReverseHistory prior) C := by
          intro C hC
          exact O.withNewRankOrder_preserves_earlier r
            (O.ordersFromReverseHistory prior) B choice n
            hRankB C hC
        have hTail :
            O.taggedPrefixFromAssignment r updated n
              (Nat.le_of_succ_le hn) =
            O.taggedPrefixFromAssignment r
              (O.ordersFromReverseHistory prior) n
              (Nat.le_of_succ_le hn) :=
          O.taggedPrefixFromAssignment_eq_of_agree r updated
            (O.ordersFromReverseHistory prior) n
            (Nat.le_of_succ_le hn) hEarlier
        have hPriorInverse :
            O.taggedPrefixFromAssignment r
              (O.ordersFromReverseHistory prior) n
              (Nat.le_of_succ_le hn) = prior :=
          ih (Nat.le_of_succ_le hn) prior hPrior
        have hBIndex :
            r.symm ⟨n, Nat.lt_of_succ_le hn⟩ = B := by
          apply congrArg r.symm
          apply Fin.ext
          exact hLen.symm
        calc
          O.taggedPrefixFromAssignment r
              (O.ordersFromReverseHistory
                ((⟨B, choice⟩ : O.TaggedComponentOrder) :: prior))
              (n + 1) hn =
            O.taggedPrefixFromAssignment r updated
              (n + 1) hn := by
                rw [hState]
          _ = (⟨B, updated B⟩ : O.TaggedComponentOrder) ::
              O.taggedPrefixFromAssignment r updated n
                (Nat.le_of_succ_le hn) := by
                simp [taggedPrefixFromAssignment, hBIndex]
          _ = (⟨B, choice⟩ : O.TaggedComponentOrder) :: prior := by
                rw [hAtB, hTail, hPriorInverse]
      · simp [canonicalTaggedNextChoices, hBound] at hTag

/-- The execution map is injective on the finite family of
complete *reachable* tagged SCC-order histories.  Distinct
histories cannot yield the same labelled canonical assignment. -/
theorem ordersFromReverseHistory_injective_on_reachable
    (r : O.ComponentRanking)
    {h₁ h₂ : List O.TaggedComponentOrder}
    (hh₁ : h₁ ∈
      BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject))
    (hh₂ : h₂ ∈
      BigHrushovski.FiniteChoiceHistory.reachableHistories
        (O.canonicalTaggedNextChoices r)
        (Fintype.card O.ComponentObject))
    (hEq : O.ordersFromReverseHistory h₁ =
      O.ordersFromReverseHistory h₂) :
    h₁ = h₂ := by
  calc
    h₁ = O.taggedPrefixFromAssignment r
        (O.ordersFromReverseHistory h₁)
        (Fintype.card O.ComponentObject) le_rfl :=
      (O.taggedPrefix_of_reachableHistory r
        (Fintype.card O.ComponentObject) le_rfl h₁ hh₁).symm
    _ = O.taggedPrefixFromAssignment r
        (O.ordersFromReverseHistory h₂)
        (Fintype.card O.ComponentObject) le_rfl := by
      rw [hEq]
    _ = h₂ := O.taggedPrefix_of_reachableHistory r
      (Fintype.card O.ComponentObject) le_rfl h₂ hh₂

end FiniteOrientation
end BigHrushovski
