import BigHrushovski.N0ReachableHistoryCanonical
import Mathlib.Tactic

/-!
# Canonical component assignments produce reachable tagged histories

Fix a legal ranking r of the actual SCCs and a complete canonical
assignment of labelled internal component orders.  Consider the
reverse-chronological tagged history of its first n components.

The history is reachable: by induction, its first n choices have
already been accepted.  At the next rank, the partial assignment
agrees with the given complete canonical assignment on every SCC
in that prefix.  Rank-prefix locality transfers the complete
canonicality condition to the partial assignment, verifying the
precise next-choice predicate.

This establishes the converse existence direction of the finite
history-to-assignment correspondence.  Injectivity of the map from
reachable histories to final assignments is treated separately.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- At rank n, the partial tagged history of a canonical complete
assignment agrees with that assignment at all SCCs ranked at
most n.  Hence the local canonical predicate on B=r⁻¹(n)
holds after executing that partial history. -/
theorem canonicalAssignment_taggedPrefix_canonicalAtNewRank
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (hCanon : O.IsCanonicalComponentAssignment r orders)
    (n : ℕ)
    (hn : n + 1 ≤ Fintype.card O.ComponentObject) :
    let B : O.ComponentObject := r.symm ⟨n, Nat.lt_of_succ_le hn⟩
    O.IsCanonicalAtComponent r
      (O.ordersFromReverseHistory
        (O.taggedPrefixFromAssignment r orders (n+1) hn))
      B := by
  let B : O.ComponentObject := r.symm ⟨n, Nat.lt_of_succ_le hn⟩
  change O.IsCanonicalAtComponent r
    (O.ordersFromReverseHistory
      (O.taggedPrefixFromAssignment r orders (n + 1) hn)) B
  have hRankB : (r B).val = n := by simp [B]
  have hAgree : O.AgreeThroughComponentRank r
      (O.ordersFromReverseHistory
        (O.taggedPrefixFromAssignment r orders (n+1) hn))
      orders (r B) := by
    intro C hC
    have hRankC : (r C).val < n + 1 := by
      change (r C).val ≤ (r B).val at hC
      omega
    exact O.ordersFrom_taggedPrefix_at_rank_lt r orders
      (n+1) hn C hRankC
  have hPrefix : O.IsCanonicalThroughRank r
      (O.ordersFromReverseHistory
        (O.taggedPrefixFromAssignment r orders (n+1) hn))
      (r B) :=
    (O.canonicalThroughRank_iff_of_prefixAgreement
      r hr
      (O.ordersFromReverseHistory
        (O.taggedPrefixFromAssignment r orders (n+1) hn))
      orders (r B) hAgree).mpr (by
        intro x _
        exact hCanon x)
  dsimp only [IsCanonicalAtComponent]
  intro x hx
  have hxB :
      (⟨O.component x, O.component_mem_components x⟩ :
        O.ComponentObject) = B :=
    Subtype.ext (O.component_eq_of_mem_componentObject B hx)
  exact hPrefix x (by rw [hxB])

/-- For a genuinely canonical complete SCC-order assignment,
the reverse-chronological list of its chosen component orders
at every consecutive rank is an actual *reachable* history
under the original next-component canonicality predicate. -/
theorem canonicalAssignment_taggedPrefix_reachable
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (hCanon : O.IsCanonicalComponentAssignment r orders) :
    ∀ n (hn : n ≤ Fintype.card O.ComponentObject),
      O.taggedPrefixFromAssignment r orders n hn ∈
        BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r) n := by
  intro n
  induction n with
  | zero =>
      intro hn
      simp [taggedPrefixFromAssignment,
        BigHrushovski.FiniteChoiceHistory.reachableHistories]
  | succ n ih =>
      intro hn
      let prior : List O.TaggedComponentOrder :=
        O.taggedPrefixFromAssignment r orders n
          (Nat.le_of_succ_le hn)
      let B : O.ComponentObject :=
        r.symm ⟨n, Nat.lt_of_succ_le hn⟩
      let tag : O.TaggedComponentOrder := ⟨B, orders B⟩
      have hPrior : prior ∈
          BigHrushovski.FiniteChoiceHistory.reachableHistories
            (O.canonicalTaggedNextChoices r) n :=
        ih (Nat.le_of_succ_le hn)
      have hLen : prior.length = n :=
        O.taggedPrefixFromAssignment_length r orders n
          (Nat.le_of_succ_le hn)
      have hBound : prior.length < Fintype.card O.ComponentObject := by
        omega
      have hB :
          r.symm ⟨prior.length, hBound⟩ = B := by
        apply congrArg r.symm
        apply Fin.ext
        exact hLen
      have hCurrent :
          O.taggedPrefixFromAssignment r orders (n+1) hn =
            tag :: prior := by
        simp [taggedPrefixFromAssignment, tag, B, prior]
      have hState :
          O.ordersFromReverseHistory (tag :: prior) =
            O.withComponentOrder
              (O.ordersFromReverseHistory prior) B (orders B) :=
        O.ordersFromReverseHistory_cons tag prior
      have hAtNew :
          O.IsCanonicalAtComponent r
            (O.withComponentOrder
              (O.ordersFromReverseHistory prior) B (orders B)) B := by
        rw [← hState, ← hCurrent]
        exact O.canonicalAssignment_taggedPrefix_canonicalAtNewRank
          r hr orders hCanon n hn
      have hChoice :
          tag ∈ O.canonicalTaggedNextChoices r prior := by
        simp only [canonicalTaggedNextChoices, dif_pos hBound]
        rw [hB]
        apply Finset.mem_image.mpr
        exact ⟨orders B,
          (O.mem_canonicalNextComponentChoices r
            (O.ordersFromReverseHistory prior) B (orders B)).mpr hAtNew,
          rfl⟩
      rw [hCurrent]
      change tag :: prior ∈
        (BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r) n).biUnion
          (fun prior => (O.canonicalTaggedNextChoices r prior).image
            (fun choice => choice :: prior))
      apply Finset.mem_biUnion.mpr
      exact ⟨prior, hPrior,
        Finset.mem_image.mpr ⟨tag, hChoice, rfl⟩⟩

/-- Every canonical complete assignment has a reachable full
tagged history which executes back to precisely that assignment,
not merely to an isomorphic ordered graph. -/
theorem canonicalAssignment_has_reachableHistory
    (r : O.ComponentRanking)
    (hr : O.IsLinearComponentRanking r)
    (orders : O.ComponentLocalEnumerations)
    (hCanon : O.IsCanonicalComponentAssignment r orders) :
    ∃ history : List O.TaggedComponentOrder,
      history ∈
        BigHrushovski.FiniteChoiceHistory.reachableHistories
          (O.canonicalTaggedNextChoices r)
          (Fintype.card O.ComponentObject) ∧
      O.ordersFromReverseHistory history = orders := by
  refine ⟨O.taggedPrefixFromAssignment r orders
    (Fintype.card O.ComponentObject) le_rfl, ?_, ?_⟩
  · exact O.canonicalAssignment_taggedPrefix_reachable r
      hr orders hCanon _ le_rfl
  · exact O.ordersFrom_completeTaggedHistory r orders

end FiniteOrientation
end BigHrushovski
