import BigHrushovski.N0UnconditionalHistoryCount
import BigHrushovski.N0CanonicalPrefixLocality
import Mathlib.Tactic

/-!
# Reconstructing an actual component assignment from its tagged history

For a fixed ranking of the actual strongly connected components, each
internal order is tagged with its component.  The chronological history
of a complete assignment is obtained by listing its tagged component
orders in ranking order, then reversing the list as required by the
reachable-history interface.

Executing this history by successive updates recovers the original
family of labelled component orders exactly, without taking a quotient
by automorphisms.  We first prove this for every rank prefix, which
also records precisely what a partial history knows.

These are finite structural lemmas, not the Ramsey theorem.  Membership
in the reachable *canonical* history set is addressed separately.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- Prepending a tagged next choice to a reverse-chronological
history executes exactly one final update of the corresponding
actual SCC. -/
theorem ordersFromReverseHistory_cons
    (choice : O.TaggedComponentOrder)
    (history : List O.TaggedComponentOrder) :
    O.ordersFromReverseHistory (choice :: history) =
      O.withComponentOrder
        (O.ordersFromReverseHistory history) choice.1 choice.2 := by
  simp [ordersFromReverseHistory, List.reverse_cons, List.foldl_append]

/-- Reverse-chronological history obtained from the first n SCCs
of a complete assignment.  Each tag contains the genuine
component carrier in rank order, and its chosen enumeration. -/
noncomputable def taggedPrefixFromAssignment
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    (n : ℕ) →
      n ≤ Fintype.card O.ComponentObject →
      List O.TaggedComponentOrder
  | 0, _ => []
  | n + 1, hn =>
      let B : O.ComponentObject :=
        r.symm ⟨n, Nat.lt_of_succ_le hn⟩
      (⟨B, orders B⟩ : O.TaggedComponentOrder) ::
        taggedPrefixFromAssignment r orders n
          (Nat.le_of_succ_le hn)

/-- A rank prefix contains exactly one choice per SCC in that
prefix, even if the local component sizes are different. -/
theorem taggedPrefixFromAssignment_length
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    ∀ n (hn : n ≤ Fintype.card O.ComponentObject),
      (O.taggedPrefixFromAssignment r orders n hn).length = n := by
  intro n
  induction n with
  | zero =>
      intro hn
      rfl
  | succ n ih =>
      intro hn
      simp [taggedPrefixFromAssignment, ih (Nat.le_of_succ_le hn)]

/-- Executing the tagged rank-prefix history recovers the exact
labelled internal order of every component already listed in
that prefix.  No claim is made about the unchosen later SCCs. -/
theorem ordersFrom_taggedPrefix_at_rank_lt
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    ∀ n (hn : n ≤ Fintype.card O.ComponentObject)
      (B : O.ComponentObject),
      (r B).val < n →
      (O.ordersFromReverseHistory
        (O.taggedPrefixFromAssignment r orders n hn)) B = orders B := by
  intro n
  induction n with
  | zero =>
      intro hn B hB
      omega
  | succ n ih =>
      intro hn B hB
      let C : O.ComponentObject :=
        r.symm ⟨n, Nat.lt_of_succ_le hn⟩
      have hC : (r C).val = n := by
        simp [C]
      have hStep :
          O.ordersFromReverseHistory
              (O.taggedPrefixFromAssignment r orders (n + 1) hn) =
            O.withComponentOrder
              (O.ordersFromReverseHistory
                (O.taggedPrefixFromAssignment r orders n
                  (Nat.le_of_succ_le hn)))
              C (orders C) := by
        exact O.ordersFromReverseHistory_cons
          (⟨C, orders C⟩ : O.TaggedComponentOrder)
          (O.taggedPrefixFromAssignment r orders n
            (Nat.le_of_succ_le hn))
      rw [hStep]
      by_cases hBC : B = C
      · subst B
        exact O.withComponentOrder_at _ C (orders C)
      · have hValNe : (r B).val ≠ n := by
          intro hv
          have hEq : r B = r C := by
            apply Fin.ext
            omega
          exact hBC (r.injective hEq)
        have hEarlier : (r B).val < n := by omega
        rw [O.withComponentOrder_other _ C B hBC (orders C)]
        exact ih (Nat.le_of_succ_le hn) B hEarlier

/-- A complete tagged history of any labelled SCC-order
assignment reconstructs that assignment *literally*.  In
particular, the history representation is surjective onto
all assignments before canonicality restrictions are imposed. -/
theorem ordersFrom_completeTaggedHistory
    (r : O.ComponentRanking)
    (orders : O.ComponentLocalEnumerations) :
    O.ordersFromReverseHistory
      (O.taggedPrefixFromAssignment r orders
        (Fintype.card O.ComponentObject) le_rfl) = orders := by
  funext B
  exact O.ordersFrom_taggedPrefix_at_rank_lt r orders
    (Fintype.card O.ComponentObject) le_rfl B (r B).isLt

end FiniteOrientation
end BigHrushovski
