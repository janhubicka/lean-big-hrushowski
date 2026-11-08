import BigHrushovski.C0CountableIntrinsicComponents

/-!
# A finite-layer construction for enumerating countable C₀ components

For a complete finite-valued unary closure on the carrier ℕ, set
Sₙ = ⋃_{i<n} C(i). These cuts are finite and closed, increase with n,
and cover every natural number. The new layer Sₙ₊₁ \ Sₙ is a union
of whole intrinsic components.

Within one finite layer, a strict component dependency lowers the
cardinality of the complete unary value. Thus rank-threshold cuts
of the layer, together with the previous Sₙ, are still C-closed.

A global ranking by closure size could starve higher-rank components
when there are infinitely many minimal ones. The finite-layer
construction has no such problem because every vertex x belongs
to S_(x+1). This file proves the finite closure facts, not yet a
literal ω-enumeration by component intervals.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The finite complete-unary closure of the first n natural labels. -/
noncomputable def unaryFiniteCut
    (C : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).biUnion C

/-- Finite cuts are monotone in n, without requiring closure axioms. -/
theorem unaryFiniteCut_mono
    (C : ℕ → Finset ℕ) {n m : ℕ} (hnm : n ≤ m) :
    unaryFiniteCut C n ⊆ unaryFiniteCut C m := by
  classical
  intro x hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hnm), hix⟩

/-- Every finite prefix of generators produces a finite C-closed set. -/
theorem unaryFiniteCut_closed
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    ∀ x ∈ unaryFiniteCut C n, C x ⊆ unaryFiniteCut C n := by
  classical
  intro x hx y hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr
    ⟨i, hi, (hC.2 i x hix) hy⟩

/-- The (n+1)-st finite cut already contains the original label n. -/
theorem mem_unaryFiniteCut_succ
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) : n ∈ unaryFiniteCut C (n+1) := by
  classical
  exact Finset.mem_biUnion.mpr
    ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), hC.1 n⟩

/-- The fresh vertices that appear between successive finite cuts. -/
noncomputable def unaryFiniteLayer
    (C : ℕ → Finset ℕ) (n : ℕ) : Finset ℕ :=
  unaryFiniteCut C (n+1) \ unaryFiniteCut C n

/-- The fresh layer contains a whole intrinsic component whenever
it contains one vertex of that component. -/
theorem unaryComponent_subset_layer
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n x : ℕ) (hx : x ∈ unaryFiniteLayer C n) :
    unaryComponent C x ⊆ unaryFiniteLayer C n := by
  classical
  intro y hy
  have hxHigh : x ∈ unaryFiniteCut C (n+1) :=
    (Finset.mem_sdiff.mp hx).1
  have hxNotLow : x ∉ unaryFiniteCut C n :=
    (Finset.mem_sdiff.mp hx).2
  have hyValue : C y = C x :=
    (mem_unaryComponent_iff C hC x y).mp hy
  have hyC : y ∈ C x := unaryComponent_subset_value C x hy
  have hyHigh : y ∈ unaryFiniteCut C (n+1) :=
    unaryFiniteCut_closed C hC (n+1) x hxHigh hyC
  have hyNotLow : y ∉ unaryFiniteCut C n := by
    intro hyLow
    have hxCy : x ∈ C y := by
      rw [hyValue]
      exact hC.1 x
    exact hxNotLow (unaryFiniteCut_closed C hC n y hyLow hxCy)
  exact Finset.mem_sdiff.mpr ⟨hyHigh, hyNotLow⟩

/-- A predecessor of a component in the fresh layer either already
belongs to an earlier finite cut or belongs to the same layer with
strictly smaller complete-closure size. -/
theorem strictLower_of_layer_old_or_smaller
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) {x y : ℕ}
    (hx : x ∈ unaryFiniteLayer C n)
    (hy : y ∈ strictLowerValue C x) :
    y ∈ unaryFiniteCut C n ∨
      (y ∈ unaryFiniteLayer C n ∧ (C y).card < (C x).card) := by
  classical
  have hxHigh : x ∈ unaryFiniteCut C (n+1) :=
    (Finset.mem_sdiff.mp hx).1
  have hyCx : y ∈ C x := (Finset.mem_sdiff.mp hy).1
  have hyHigh : y ∈ unaryFiniteCut C (n+1) :=
    unaryFiniteCut_closed C hC (n+1) x hxHigh hyCx
  by_cases hyLow : y ∈ unaryFiniteCut C n
  · exact Or.inl hyLow
  · exact Or.inr
      ⟨Finset.mem_sdiff.mpr ⟨hyHigh, hyLow⟩,
       strictLowerValue_card_lt C hC hy⟩

/-- The finite C-closed set obtained by processing the new layer
up to a given complete-closure rank. No component is split by a
rank threshold, because all its vertices have the same full value. -/
noncomputable def unaryFiniteRankCut
    (C : ℕ → Finset ℕ) (n rank : ℕ) : Finset ℕ :=
  unaryFiniteCut C n ∪
    (unaryFiniteLayer C n).filter (fun x => (C x).card ≤ rank)

/-- Every finite rank-threshold cut is closed under the *complete*
unary operation, not just under one-step backward neighbours. -/
theorem unaryFiniteRankCut_closed
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n rank : ℕ) :
    ∀ x ∈ unaryFiniteRankCut C n rank,
      C x ⊆ unaryFiniteRankCut C n rank := by
  classical
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hxOld | hxNew
  · exact Finset.mem_union.mpr (Or.inl
      (unaryFiniteCut_closed C hC n x hxOld hy))
  · obtain ⟨hxLayer, hxRank⟩ := Finset.mem_filter.mp hxNew
    have hxHigh : x ∈ unaryFiniteCut C (n+1) :=
      (Finset.mem_sdiff.mp hxLayer).1
    by_cases hyOld : y ∈ unaryFiniteCut C n
    · exact Finset.mem_union.mpr (Or.inl hyOld)
    · have hyHigh : y ∈ unaryFiniteCut C (n+1) :=
        unaryFiniteCut_closed C hC (n+1) x hxHigh hy
      have hyLayer : y ∈ unaryFiniteLayer C n :=
        Finset.mem_sdiff.mpr ⟨hyHigh, hyOld⟩
      have hCard : (C y).card ≤ (C x).card :=
        Finset.card_le_card (hC.2 x y hy)
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hyLayer, by omega⟩))

/-- Finite layers together with their predecessors exhaust the
whole (n+1)-st finite closed cut, by literal set equality. -/
theorem unaryFiniteCut_succ_eq_union_layer
    (C : ℕ → Finset ℕ) (n : ℕ) :
    unaryFiniteCut C (n+1) =
      unaryFiniteCut C n ∪ unaryFiniteLayer C n := by
  classical
  have hMono : unaryFiniteCut C n ⊆ unaryFiniteCut C (n+1) :=
    unaryFiniteCut_mono C (Nat.le_succ n)
  ext x
  constructor
  · intro hx
    by_cases hxOld : x ∈ unaryFiniteCut C n
    · exact Finset.mem_union.mpr (Or.inl hxOld)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxOld⟩))
  · intro hx
    rcases Finset.mem_union.mp hx with hOld | hNew
    · exact hMono hOld
    · exact (Finset.mem_sdiff.mp hNew).1

end FiniteC0
end BigHrushovski
