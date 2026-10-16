import BigHrushovski.CFGrowthCutoff

/-!
# The exact generalized inverse of a monotone unbounded integer growth function

For a monotone unbounded F: ℕ→ℝ with F(0)=0, the
finite set of integers n with F(n)≤2(k+1) has a greatest
member. It equals one less than the first index at
which F exceeds the threshold.

The previous conservative cutoff is therefore improved to
the exact generalized inverse at this threshold. Flat
intervals cause no difficulty; continuity or strict
monotonicity is not assumed.

We separately retain the monotonicity and integer-
unboundedness hypotheses. They are satisfied by the
restriction to natural arguments of the continuous
nondecreasing unbounded function used in the manuscript.
-/

namespace BigHrushovski
namespace CFGrowthNumerics

/-- Greatest integral size allowed by the inequality
F(n)≤2(k+1). The strict cutoff is nonzero because F(0)=0. -/
noncomputable def growthInverseSize
    (F : ℕ → ℝ)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k : ℕ) : ℕ :=
  sizeCutoff F hUnbounded k - 1

/-- The first index exceeding a nonnegative threshold is
positive when F(0)=0. -/
theorem sizeCutoff_pos
    (F : ℕ → ℝ)
    (hZero : F 0 = 0)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k : ℕ) :
    0 < sizeCutoff F hUnbounded k := by
  by_contra hn
  have hc : sizeCutoff F hUnbounded k = 0 := by omega
  have hStrict := sizeCutoff_spec F hUnbounded k
  rw [hc, hZero] at hStrict
  have hNonneg : (0 : ℝ) ≤
      2 * (((k + 1 : ℕ) : ℝ)) := by positivity
  linarith

/-- The exact integral inverse itself satisfies the
threshold inequality. This is the minimality property
of Nat.find applied just below the first strict crossing. -/
theorem growthInverseSize_admissible
    (F : ℕ → ℝ)
    (hZero : F 0 = 0)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k : ℕ) :
    F (growthInverseSize F hUnbounded k) ≤
      2 * (((k + 1 : ℕ) : ℝ)) := by
  let T : ℝ := 2 * (((k + 1 : ℕ) : ℝ))
  have hCutPos := sizeCutoff_pos F hZero hUnbounded k
  have hLess :
      growthInverseSize F hUnbounded k <
        sizeCutoff F hUnbounded k := by
    dsimp [growthInverseSize]
    omega
  have hNot :
      ¬ T < F (growthInverseSize F hUnbounded k) := by
    exact Nat.find_min'
      (hUnbounded T)
      (growthInverseSize F hUnbounded k)
      hLess
  exact le_of_not_gt hNot

/-- Membership in the finite growth interval is *equivalent*
to being at most the generalized inverse. This explicitly
handles possible equality and flat portions of F. -/
theorem growthInverseSize_iff
    (F : ℕ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k n : ℕ) :
    F n ≤ 2 * (((k + 1 : ℕ) : ℝ)) ↔
      n ≤ growthInverseSize F hUnbounded k := by
  constructor
  · intro hn
    have hBefore :=
      growthSize_below_cutoff F hMono hUnbounded k n hn
    dsimp [growthInverseSize]
    omega
  · intro hn
    exact (hMono hn).trans
      (growthInverseSize_admissible F hZero hUnbounded k)

/-- The exact generalized inverse is now a valid size bound for
every minimal strict C_F extension, using no additional
inverse hypothesis beyond monotonicity, unboundedness
and F(0)=0. -/
theorem minimal_growth_size_with_inverse
    {V : Type*} [DecidableEq V]
    (G : GraphOn V)
    (F : ℕ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (a b : Finset V)
    (hMin : G.toPredimension.IsMinimalDClosedStep a b)
    (hGrowth : G.IsGrowthSparse F b)
    (x : V) (hxb : x ∈ b) (hxna : x ∉ a) :
    b.card ≤ growthInverseSize F hUnbounded a.card := by
  exact G.minimal_growth_extension_card_le F
    (growthInverseSize F hUnbounded)
    (fun k n hFn =>
      (growthInverseSize_iff
        F hZero hMono hUnbounded k n).mp hFn)
    a b hMin hGrowth x hxb hxna

end CFGrowthNumerics
end BigHrushovski
