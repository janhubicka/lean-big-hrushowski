import BigHrushovski.CFFiniteLevelOrderRigidity

/-!
# The C_F order on finite stages is the restriction of the birth order

The finite tower is constructed with a recursively inherited linear
order. Its countable birth-labelled carrier carries the canonical
level/request/ordinal order. We now compare these two *particular*
orders through the existing literal maps U_n → M_F^dagger.

This compatibility is needed for unique level lifting: an induced
map into a target stage must preserve exactly the same order as the
eventual map into the countable birth structure. The proof uses
the verified old/fresh successor comparison, not an arbitrary
choice of order on the stages or on the limit.

No finite level lifting or embedding-monoid conclusion is asserted.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- A strict comparison in the canonical countable birth order
never decreases the birth level. -/
theorem canonicalBirthLt_birthLevel_le
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (u v : Vertex F K)
    (h : canonicalBirthLt F K u v) :
    u.1 ≤ v.1 := by
  rcases u with ⟨n, ⟨r, i⟩⟩
  rcases v with ⟨m, ⟨s, j⟩⟩
  dsimp [canonicalBirthLt, rankedBirthLt,
    birthOrderKey, tripleLexLt] at h
  rcases h with h | ⟨h, _⟩ <;> omega

/-- The strict order of one stage is asymmetric, because it was
obtained from an actual linear order, not merely a preorder. -/
theorem stageLt_asymm
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (u v : (stage F K n).carrier)
    (h : stageLt F K n u v) :
    ¬ stageLt F K n v u := by
  intro h'
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  have huv : u < v := h
  have hvu : v < u := h'
  exact (lt_asymm huv hvu)

/-- Exact order coherence between the recursively defined
finite-stage orders and the manuscript's countable birth order.
The map is the literal birth map, with no renumbering of vertices. -/
theorem stageLt_iff_canonicalBirthLt
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    ∀ u v : (stage F K n).carrier,
      stageLt F K n u v ↔
        canonicalBirthLt F K (toVertex F K n u)
          (toVertex F K n v) := by
  induction n with
  | zero =>
      intro u v
      exact Fin.elim0 u
  | succ n ih =>
      intro u v
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              simpa only [toVertex_old] using
                ((stageOrder_old_iff F K n u v).trans (ih u v))
          | inr v =>
              have hOldBorn : (toVertex F K n u).1 < n :=
                toVertex_birth_lt F K n u
              have hBirth :
                  canonicalBirthLt F K
                    (toVertex F K (n + 1) (Sum.inl u))
                    (toVertex F K (n + 1) (Sum.inr v)) :=
                rankedBirthLt_of_earlier F K (stageCanonicalRank F K)
                  (toVertex F K n u) (⟨n, v⟩ : Vertex F K)
                  hOldBorn
              exact ⟨fun _ => hBirth,
                fun _ => stageOrder_old_lt_fresh F K n u v⟩
      | inr u =>
          cases v with
          | inl v =>
              have hOldFresh : stageLt F K (n + 1)
                  (Sum.inl v) (Sum.inr u) :=
                stageOrder_old_lt_fresh F K n v u
              have hNotStage : ¬ stageLt F K (n + 1)
                  (Sum.inr u) (Sum.inl v) :=
                stageLt_asymm F K (n + 1)
                  (Sum.inl v) (Sum.inr u) hOldFresh
              have hNotBirth :
                  ¬ canonicalBirthLt F K
                    (toVertex F K (n + 1) (Sum.inr u))
                    (toVertex F K (n + 1) (Sum.inl v)) := by
                intro h
                have hl := canonicalBirthLt_birthLevel_le F K _ _ h
                have hn : n ≤ (toVertex F K n v).1 := hl
                have hOld := toVertex_birth_lt F K n v
                omega
              exact iff_of_false hNotStage hNotBirth
          | inr v =>
              rcases u with ⟨r, i⟩
              rcases v with ⟨s, j⟩
              simpa [canonicalBirthLt, rankedBirthLt,
                birthOrderKey, tripleLexLt] using
                (stageOrder_fresh_iff F K n r s i j)

/-- Coherence under any finite number of successor inclusions:
the exact finite-stage order is preserved and reflected. -/
theorem stageLt_ascend_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n k : ℕ) (u v : (stage F K n).carrier) :
    stageLt F K (n + k)
      (ascend F K n k u) (ascend F K n k v) ↔
        stageLt F K n u v := by
  calc
    stageLt F K (n + k)
        (ascend F K n k u) (ascend F K n k v) ↔
      canonicalBirthLt F K
        (toVertex F K (n + k) (ascend F K n k u))
        (toVertex F K (n + k) (ascend F K n k v)) :=
      stageLt_iff_canonicalBirthLt F K (n + k) _ _
    _ ↔ canonicalBirthLt F K (toVertex F K n u)
        (toVertex F K n v) := by
          rw [toVertex_ascend, toVertex_ascend]
    _ ↔ stageLt F K n u v :=
      (stageLt_iff_canonicalBirthLt F K n u v).symm

end CFCoherentTower
end BigHrushovski
