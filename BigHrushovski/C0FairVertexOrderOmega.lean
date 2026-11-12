import BigHrushovski.C0FairComponentBirthIndex

/-!
# Track A: a strict order of type ω from the fair intrinsic components

Take the certified fair component births and any assignment of numeric
local keys which is injective on each intrinsic component. Order first
by component birth stage and then by local key.

This yields a strict total order without a greatest vertex. The set
of predecessors of each vertex is finite, as it is contained in the
finite prefix ending with that vertex's component. Every Q_n is an
initial segment, and each entire intrinsic component is an interval.

These are the order-theoretic ingredients for a vertex enumeration of
type ω. The hypotheses deliberately leave the choice of the local
order to a separate uniform ordered-representative construction.
Taking the vertex labels as local keys gives an example but is NOT
the canonical ordered expansion used in the manuscript.
-/

namespace BigHrushovski
namespace FiniteC0

/-- Lexicographic chronology: birth components first, then the
chosen local key inside each component. -/
def fairVertexBefore
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x y : ℕ) : Prop :=
  fairComponentBirth C hC x < fairComponentBirth C hC y ∨
    (fairComponentBirth C hC x = fairComponentBirth C hC y ∧
      localKey x < localKey y)

theorem fairVertexBefore_irrefl
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x : ℕ) :
    ¬ fairVertexBefore C hC localKey x x := by
  intro h
  rcases h with hBirth | ⟨_, hKey⟩
  · exact (lt_irrefl _) hBirth
  · exact (lt_irrefl _) hKey

theorem fairVertexBefore_trans
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) {x y z : ℕ}
    (hxy : fairVertexBefore C hC localKey x y)
    (hyz : fairVertexBefore C hC localKey y z) :
    fairVertexBefore C hC localKey x z := by
  rcases hxy with hbxy | ⟨hexy, hkxy⟩
  · rcases hyz with hbyz | ⟨heyz, _⟩
    · exact Or.inl (lt_trans hbxy hbyz)
    · exact Or.inl (heyz ▸ hbxy)
  · rcases hyz with hbyz | ⟨heyz, hkyz⟩
    · exact Or.inl (hexy ▸ hbyz)
    · exact Or.inr ⟨hexy.trans heyz, lt_trans hkxy hkyz⟩

/-- A local numbering need only be injective *within each birth
component*. It need not be a global injection, and no canonical
representatives are assumed. -/
theorem fairVertexBefore_total
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    (hLocal : ∀ x y : ℕ,
      fairComponentBirth C hC x = fairComponentBirth C hC y →
      localKey x = localKey y → x = y)
    {x y : ℕ} (hxy : x ≠ y) :
    fairVertexBefore C hC localKey x y ∨
      fairVertexBefore C hC localKey y x := by
  by_cases hx : fairComponentBirth C hC x <
      fairComponentBirth C hC y
  · exact Or.inl (Or.inl hx)
  by_cases hy : fairComponentBirth C hC y <
      fairComponentBirth C hC x
  · exact Or.inr (Or.inl hy)
  have hb : fairComponentBirth C hC x =
      fairComponentBirth C hC y := by omega
  have hkey : localKey x ≠ localKey y := by
    intro heq
    exact hxy (hLocal x y hb heq)
  by_cases hk : localKey x < localKey y
  · exact Or.inl (Or.inr ⟨hb, hk⟩)
  · exact Or.inr (Or.inr ⟨hb.symm, by omega⟩)

/-- Every Q_n is an initial segment for the fair vertex order,
regardless of the chosen (injective) local ordering. -/
theorem fairVertexBefore_prefix_initial
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    {n x y : ℕ}
    (hy : y ∈ fairComponentPrefix C hC n)
    (hxy : fairVertexBefore C hC localKey x y) :
    x ∈ fairComponentPrefix C hC n := by
  have hyBirth : fairComponentBirth C hC y < n :=
    (fairComponentBirth_lt_iff_mem C hC n y).mpr hy
  have hxBirth : fairComponentBirth C hC x < n := by
    rcases hxy with hlt | ⟨heq, _⟩
    · omega
    · omega
  exact (fairComponentBirth_lt_iff_mem C hC n x).mp hxBirth

/-- Each intrinsic component is convex: a vertex strictly between
two vertices born together must have the same birth stage. -/
theorem fairVertexBefore_same_component_convex
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    {x y z : ℕ}
    (hxz : fairComponentBirth C hC x =
      fairComponentBirth C hC z)
    (hxy : fairVertexBefore C hC localKey x y)
    (hyz : fairVertexBefore C hC localKey y z) :
    fairComponentBirth C hC y = fairComponentBirth C hC x := by
  rcases hxy with hltxy | ⟨heqxy, _⟩
  · rcases hyz with hltyz | ⟨heqyz, _⟩
    · omega
    · omega
  · rcases hyz with hltyz | ⟨heqyz, _⟩
    · omega
    · exact heqxy.symm

/-- All vertices preceding x lie in the finite prefix at the end
of x's own component, independently of the chosen local keys. -/
theorem fairVertexBefore_predecessor_in_prefix
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ)
    {x y : ℕ}
    (hyx : fairVertexBefore C hC localKey y x) :
    y ∈ fairComponentPrefix C hC
      (fairComponentBirth C hC x + 1) := by
  have hlt :
      fairComponentBirth C hC y <
        fairComponentBirth C hC x + 1 := by
    rcases hyx with hBirth | ⟨hBirth, _⟩
    · omega
    · omega
  exact (fairComponentBirth_lt_iff_mem C hC
    (fairComponentBirth C hC x + 1) y).mp hlt

/-- The exact set of predecessors of x, represented as a finite set
without imposing any linear-order instance on the natural carrier. -/
noncomputable def fairVertexPredecessors
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (fairComponentPrefix C hC
    (fairComponentBirth C hC x + 1)).filter
      (fun y => fairVertexBefore C hC localKey y x)

theorem mem_fairVertexPredecessors_iff
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x y : ℕ) :
    y ∈ fairVertexPredecessors C hC localKey x ↔
      fairVertexBefore C hC localKey y x := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨fairVertexBefore_predecessor_in_prefix C hC localKey h, h⟩

/-- No vertex is last: the finite prefix through its component
does not exhaust ℕ, so a later component always exists. -/
theorem fairVertexBefore_no_greatest
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (localKey : ℕ → ℕ) (x : ℕ) :
    ∃ y : ℕ, fairVertexBefore C hC localKey x y := by
  let n := fairComponentBirth C hC x + 1
  obtain ⟨y, hyNot, _⟩ :=
    exists_enabledVertex C hC (fairComponentPrefix C hC n)
  have hyBound : n ≤ fairComponentBirth C hC y := by
    by_contra h
    have hyMem : y ∈ fairComponentPrefix C hC n :=
      (fairComponentBirth_lt_iff_mem C hC n y).mp (by omega)
    exact hyNot hyMem
  refine ⟨y, Or.inl ?_⟩
  dsimp [n] at hyBound
  omega

/-- Raw numerical vertex labels give one concrete injective local
numbering. This order is *not* asserted to be the uniform canonical
ordered expansion of the paper. -/
theorem fairVertexBefore_numeric_total
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    {x y : ℕ} (hxy : x ≠ y) :
    fairVertexBefore C hC id x y ∨ fairVertexBefore C hC id y x := by
  apply fairVertexBefore_total C hC id
  · intro a b _ hab
    exact hab
  · exact hxy

end FiniteC0
end BigHrushovski
