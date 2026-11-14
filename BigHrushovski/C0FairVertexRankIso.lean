import BigHrushovski.C0FairVertexOrderOmega

/-!
# Track A: the fair vertex order is explicitly of order type ω

For a fair component chronology with any injective local numbering,
let r(x) be the cardinality of the finite set of vertices preceding x.
The strict order makes predecessor sets strictly nested, so r is
injective and strictly order preserving.

More precisely, the images of the predecessors of x under r form
exactly {0,...,r(x)-1}. Starting at rank zero and using the fact that
the vertex order has no greatest point, this proves that every natural
number is attained as a rank. Thus the rank map is an actual
bijection of the vertices with ℕ, identifying the fair vertex order
with the usual order of ℕ.

This theorem does NOT choose the local numberings required by the
paper's uniform ordered representative convention. It applies to
any future choice meeting the stated componentwise injectivity.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The number of earlier vertices in the fair strict order. -/
noncomputable def fairVertexRank
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x : ℕ) : ℕ :=
  (fairVertexPredecessors C hC localKey x).card

/-- Predecessors of x form a strict subset of the predecessors of y
whenever x precedes y: every predecessor of x precedes y, and x
itself belongs only to the latter predecessor set. -/
theorem fairVertexPredecessors_ssubset
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    {x y : ℕ} (hxy : fairVertexBefore C hC localKey x y) :
    fairVertexPredecessors C hC localKey x ⊂
      fairVertexPredecessors C hC localKey y := by
  classical
  have hSub :
      fairVertexPredecessors C hC localKey x ⊆
        fairVertexPredecessors C hC localKey y := by
    intro z hz
    apply (mem_fairVertexPredecessors_iff C hC localKey y z).mpr
    exact fairVertexBefore_trans C hC localKey
      ((mem_fairVertexPredecessors_iff C hC localKey x z).mp hz)
      hxy
  have hNe :
      fairVertexPredecessors C hC localKey x ≠
        fairVertexPredecessors C hC localKey y := by
    intro heq
    have hx : x ∈ fairVertexPredecessors C hC localKey y :=
      (mem_fairVertexPredecessors_iff C hC localKey y x).mpr hxy
    rw [← heq] at hx
    exact (fairVertexBefore_irrefl C hC localKey x)
      ((mem_fairVertexPredecessors_iff C hC localKey x x).mp hx)
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩

theorem fairVertexRank_lt_of_before
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    {x y : ℕ} (hxy : fairVertexBefore C hC localKey x y) :
    fairVertexRank C hC localKey x <
      fairVertexRank C hC localKey y :=
  Finset.card_lt_card
    (fairVertexPredecessors_ssubset C hC localKey hxy)

/-- The strict totality of the fair order makes rank injective. -/
theorem fairVertexRank_injective
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y) :
    Function.Injective (fairVertexRank C hC localKey) := by
  intro x y heq
  by_contra hNe
  rcases fairVertexBefore_total C hC localKey hLocal hNe with hxy | hyx
  · have hlt := fairVertexRank_lt_of_before C hC localKey hxy
    omega
  · have hlt := fairVertexRank_lt_of_before C hC localKey hyx
    omega

/-- The ranks of the vertices preceding x are exactly the
consecutive natural numbers below r(x). This is a finite
cardinality argument, not an assumption about the order type. -/
theorem fairVertexRank_image_predecessors
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y)
    (x : ℕ) :
    (fairVertexPredecessors C hC localKey x).image
      (fairVertexRank C hC localKey) =
        Finset.range (fairVertexRank C hC localKey x) := by
  classical
  let P := fairVertexPredecessors C hC localKey x
  let r := fairVertexRank C hC localKey
  have hinj : Function.Injective r :=
    fairVertexRank_injective C hC localKey hLocal
  have hSub : P.image r ⊆ Finset.range (r x) := by
    intro k hk
    obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp hk
    have hBefore : fairVertexBefore C hC localKey y x :=
      (mem_fairVertexPredecessors_iff C hC localKey x y).mp hy
    have hLt : r y < r x :=
      fairVertexRank_lt_of_before C hC localKey hBefore
    exact Finset.mem_range.mpr (by rw [← hEq]; exact hLt)
  have hCard : (Finset.range (r x)).card ≤ (P.image r).card := by
    rw [Finset.card_range, Finset.card_image_of_injective P hinj]
    rfl
  exact Finset.eq_of_subset_of_card_le hSub hCard

/-- Every smaller natural rank occurs at an actual predecessor. -/
theorem fairVertexRank_lower_realized
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y)
    (x k : ℕ) (hk : k < fairVertexRank C hC localKey x) :
    ∃ y : ℕ,
      fairVertexBefore C hC localKey y x ∧
      fairVertexRank C hC localKey y = k := by
  classical
  have himg :=
    fairVertexRank_image_predecessors C hC localKey hLocal x
  have hkMem :
      k ∈ (fairVertexPredecessors C hC localKey x).image
        (fairVertexRank C hC localKey) := by
    rw [himg]
    exact Finset.mem_range.mpr hk
  obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hkMem
  exact ⟨y,
    (mem_fairVertexPredecessors_iff C hC localKey x y).mp hy,
    hyr⟩

/-- No natural rank is skipped. The case zero follows by looking at
the finite predecessors of vertex 0; a later rank is obtained from
a vertex above any one of the previous rank. -/
theorem fairVertexRank_surjective
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y) :
    Function.Surjective (fairVertexRank C hC localKey) := by
  intro k
  induction k with
  | zero =>
      by_cases hZero : fairVertexRank C hC localKey 0 = 0
      · exact ⟨0, hZero⟩
      · have hPos : 0 < fairVertexRank C hC localKey 0 := by omega
        obtain ⟨y, _, hy⟩ :=
          fairVertexRank_lower_realized C hC localKey hLocal 0 0 hPos
        exact ⟨y, hy⟩
  | succ k ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hxy⟩ := fairVertexBefore_no_greatest
        C hC localKey x
      have hlt := fairVertexRank_lt_of_before C hC localKey hxy
      by_cases heq : fairVertexRank C hC localKey y = k + 1
      · exact ⟨y, heq⟩
      · have hk : k + 1 < fairVertexRank C hC localKey y := by omega
        obtain ⟨z, _, hz⟩ :=
          fairVertexRank_lower_realized C hC localKey hLocal
            y (k + 1) hk
        exact ⟨z, hz⟩

theorem fairVertexRank_bijective
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y) :
    Function.Bijective (fairVertexRank C hC localKey) :=
  ⟨fairVertexRank_injective C hC localKey hLocal,
    fairVertexRank_surjective C hC localKey hLocal⟩

/-- The rank comparison reflects and preserves the entire strict
fair vertex order, not just the birth components. -/
theorem fairVertexBefore_iff_rank_lt
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y)
    (x y : ℕ) :
    fairVertexBefore C hC localKey x y ↔
      fairVertexRank C hC localKey x <
        fairVertexRank C hC localKey y := by
  constructor
  · exact fairVertexRank_lt_of_before C hC localKey
  · intro hlt
    by_cases hxy : x = y
    · subst y
      omega
    rcases fairVertexBefore_total C hC localKey hLocal hxy with hBefore | hBack
    · exact hBefore
    · have hOpp := fairVertexRank_lt_of_before
        C hC localKey hBack
      omega

/-- An explicit bijection to ℕ whose ordinary comparison is precisely
the selected fair strict vertex order. This realizes order type ω.
The local keys remain an external choice. -/
noncomputable def fairVertexRankEquiv
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y) : ℕ ≃ ℕ :=
  Equiv.ofBijective (fairVertexRank C hC localKey)
    (fairVertexRank_bijective C hC localKey hLocal)

theorem fairVertexBefore_iff_rankEquiv_lt
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y)
    (x y : ℕ) :
    fairVertexBefore C hC localKey x y ↔
      fairVertexRankEquiv C hC localKey hLocal x <
        fairVertexRankEquiv C hC localKey hLocal y :=
  fairVertexBefore_iff_rank_lt C hC localKey hLocal x y

end FiniteC0
end BigHrushovski
