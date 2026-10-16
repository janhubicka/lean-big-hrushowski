import BigHrushovski.CFExactGrowthInverse

/-!
# Restrict monotone unbounded real growth to integer cardinalities

The published C_F definition uses a continuous nondecreasing
unbounded growth function on nonnegative real arguments.
The finite graph predimension construction evaluates this
function only at natural cardinalities.

The analytic assumptions needed for the numerical finite-size
bound are exactly monotonicity, F(0)=0, and unboundedness.
The Archimedean property of the real numbers shows that the
restriction n ↦ F(n) to natural arguments remains unbounded:
for any real threshold, choose a sufficiently large real x
above it in F-value and then an integer n>x.

This module isolates that elementary numerical bridge. It
does not use continuity, and hence applies to the more
general monotone unbounded functions considered in the paper.
-/

namespace BigHrushovski
namespace CFGrowthNumerics

/-- Monotonicity of a real growth function is inherited by
its restriction to natural cardinalities. -/
theorem realGrowth_nat_monotone
    (F : ℝ → ℝ) (hMono : Monotone F) :
    Monotone (fun n : ℕ => F (n : ℝ)) := by
  intro a b hab
  apply hMono
  exact_mod_cast hab

/-- Unbounded monotone real growth remains unbounded at
integer cardinalities by the Archimedean property of ℝ.
Only growth along real arguments is needed. -/
theorem realGrowth_nat_unbounded
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) :
    ∀ t : ℝ, ∃ n : ℕ, t < F (n : ℝ) := by
  intro t
  obtain ⟨x, hx⟩ := hUnbounded t
  obtain ⟨n, hxn⟩ := exists_nat_gt x
  refine ⟨n, ?_⟩
  exact hx.trans_le (hMono (le_of_lt hxn))

/-- The exact integer generalized inverse of the
restriction of real growth bounds every finite minimal
strict d-closed extension in the growth class. -/
theorem minimal_growth_size_of_real_growth
    {V : Type*} [DecidableEq V]
    (G : GraphOn V) (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (a b : Finset V)
    (hMin : G.toPredimension.IsMinimalDClosedStep a b)
    (hGrowth : G.IsGrowthSparse (fun n : ℕ => F (n : ℝ)) b)
    (x : V) (hxb : x ∈ b) (hxna : x ∉ a) :
    b.card ≤ growthInverseSize (fun n : ℕ => F (n : ℝ))
      (realGrowth_nat_unbounded F hMono hUnbounded)
      a.card := by
  exact minimal_growth_size_with_inverse G
    (fun n : ℕ => F (n : ℝ))
    hZero
    (realGrowth_nat_monotone F hMono)
    (realGrowth_nat_unbounded F hMono hUnbounded)
    a b hMin hGrowth x hxb hxna

end CFGrowthNumerics
end BigHrushovski
