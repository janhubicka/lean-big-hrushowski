import BigHrushovski.C0CanonicalOrderInvariance

/-!
# Reconcile independent C0 base-component orders in a tagged join

The left factor has components P ⊕ L, the right factor has P ⊕ R.
Both identify P as their common closed base. Keep ALL left components
in their original order and append only fresh right components.
The two factors may order the P components differently.

For right-factor graph edges this joined order agrees with the
right original orientation, provided:
  1. the left component ranks are below a chosen finite bound;
  2. P was frontloaded before R in the right factor; and
  3. both orderings orient each P--P graph edge identically.

Condition (3) follows from the common complete unary values by the
already checked intrinsic-component and edge-orientation lemmas.
Thus the exact dependency graph and complete canonical unary values
of the right factor are not changed by the joined chronological order.

This module is the finite arithmetic order reconciliation; the actual
graph/minimal-step and complete-fibre transport are proved separately.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}

/-- Keep the old left ranks and append each new right component after
the entire left factor. Ranks need not be consecutive; unused levels
can be omitted from a minimal-component presentation. -/
def joinedRank
    (rankL : Sum P L → Nat)
    (rankR : Sum P R → Nat)
    (bound : Nat) : Carrier P L R → Nat
  | .inl p => rankL (.inl p)
  | .inr (.inl l) => rankL (.inr l)
  | .inr (.inr r) => bound + rankR (.inr r)

theorem joinedRank_left
    (rankL : Sum P L → Nat)
    (rankR : Sum P R → Nat) (bound : Nat)
    (i : Sum P L) :
    joinedRank rankL rankR bound (leftTag i) = rankL i := by
  cases i <;> rfl

theorem joinedRank_right_tail
    (rankL : Sum P L → Nat)
    (rankR : Sum P R → Nat) (bound : Nat) (r : R) :
    joinedRank rankL rankR bound (rightTag (.inr r)) =
      bound + rankR (.inr r) := rfl

/-- The joined component chronology preserves every edge orientation
of the right factor, even though its P-components are ordered as in
the left factor. No comparison of unrelated P-component pairs is needed. -/
theorem joinedRank_right_edge_orientation
    (rankL : Sum P L → Nat)
    (rankR : Sum P R → Nat)
    (bound : Nat)
    (hBound : ∀ i : Sum P L, rankL i < bound)
    (hFront : ∀ p : P, ∀ r : R,
      rankR (.inl p) < rankR (.inr r))
    (rightEdge : Sum P R → Sum P R → Prop)
    (hBaseOrient : ∀ p q : P,
      rightEdge (.inl p) (.inl q) →
      (rankL (.inl p) < rankL (.inl q) ↔
       rankR (.inl p) < rankR (.inl q)))
    (x y : Sum P R) (hEdge : rightEdge x y) :
    joinedRank rankL rankR bound (rightTag x) <
        joinedRank rankL rankR bound (rightTag y) ↔
      rankR x < rankR y := by
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          exact hBaseOrient p q hEdge
      | inr r =>
          have hx := hBound (.inl p)
          have hy := hFront p r
          constructor
          · intro _
            exact hy
          · intro _
            change rankL (.inl p) < bound + rankR (.inr r)
            omega
  | inr r =>
      cases y with
      | inl p =>
          have hx := hBound (.inl p)
          have hy := hFront p r
          constructor
          · intro h
            change bound + rankR (.inr r) <
              rankL (.inl p) at h
            omega
          · intro h
            omega
      | inr s =>
          change (bound + rankR (.inr r) <
            bound + rankR (.inr s)) ↔
            rankR (.inr r) < rankR (.inr s)
          omega

/-- Component ranks on the left are unchanged, so all left-factor
graph edge directions remain unchanged without any hypothesis. -/
theorem joinedRank_left_edge_orientation
    (rankL : Sum P L → Nat)
    (rankR : Sum P R → Nat)
    (bound : Nat)
    (x y : Sum P L) :
    joinedRank rankL rankR bound (leftTag x) <
        joinedRank rankL rankR bound (leftTag y) ↔
      rankL x < rankL y := by
  rw [joinedRank_left, joinedRank_left]

end TaggedAmalgam
end BigHrushovski
