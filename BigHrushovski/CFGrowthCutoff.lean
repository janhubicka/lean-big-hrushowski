import BigHrushovski.CFMinimalGrowthSize

/-!
# A canonical finite upper bound from a monotone unbounded growth function

For a monotone function F : ℕ → ℝ unbounded above, let
cutoff(k) be the least natural number n for which

  F(n) > 2(k+1).

Such an n exists by unboundedness. By monotonicity, no
natural number m ≥ cutoff(k) can satisfy
F(m) ≤ 2(k+1). In particular the deliberately generous
bound K(k)=cutoff(k) has the inverse property needed by
the finite C_F minimal-extension size theorem.

This avoids choosing a separate arbitrary inverse-bound
function. The bound is intentionally conservative: the
strict cut-off is at most one above the largest admissible
integer cardinality, and monotonicity suffices even when
F has flat intervals.

The published function is defined over nonnegative real
arguments. Here F is its restriction to integers; deriving
the integer-unboundedness hypothesis from the published
real hypotheses is an elementary separate numerical bridge.
-/

namespace BigHrushovski
namespace CFGrowthNumerics

/-- First integer index at which F exceeds 2(k+1).
Its existence uses exactly integer-unbounded growth. -/
noncomputable def sizeCutoff
    (F : ℕ → ℝ)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k : ℕ) : ℕ :=
  Nat.find (hUnbounded (2 * (((k + 1 : ℕ) : ℝ))))

/-- The size cutoff exceeds the threshold in F value. -/
theorem sizeCutoff_spec
    (F : ℕ → ℝ)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k : ℕ) :
    2 * (((k + 1 : ℕ) : ℝ)) <
      F (sizeCutoff F hUnbounded k) :=
  Nat.find_spec (hUnbounded (2 * (((k + 1 : ℕ) : ℝ))))

/-- Any n whose F-value is below the threshold lies
strictly before the first index exceeding that threshold. -/
theorem growthSize_below_cutoff
    (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (k n : ℕ)
    (hFn : F n ≤ 2 * (((k + 1 : ℕ) : ℝ))) :
    n < sizeCutoff F hUnbounded k := by
  by_contra hn
  have hCut : sizeCutoff F hUnbounded k ≤ n := by
    omega
  have hIncreasing :
      F (sizeCutoff F hUnbounded k) ≤ F n :=
    hMono hCut
  have hAbove := sizeCutoff_spec F hUnbounded k
  linarith

/-- The automatically defined size bound has precisely the
inverse domination property assumed by the finite
minimal-extension growth-size theorem. -/
theorem sizeCutoff_inverse_property
    (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n) :
    ∀ k n : ℕ,
      F n ≤ 2 * (((k + 1 : ℕ) : ℝ)) →
        n ≤ sizeCutoff F hUnbounded k := by
  intro k n hFn
  exact Nat.le_of_lt
    (growthSize_below_cutoff F hMono hUnbounded k n hFn)

/-- No independent numerical inverse hypothesis is now
needed for the complete minimal-growth-extension bound:
monotone integer-unbounded F supplies a canonical K. -/
theorem minimal_growth_size_with_cutoff
    {V : Type*} [DecidableEq V]
    (G : GraphOn V)
    (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (a b : Finset V)
    (hMin : G.toPredimension.IsMinimalDClosedStep a b)
    (hGrowth : G.IsGrowthSparse F b)
    (x : V) (hxb : x ∈ b) (hxna : x ∉ a) :
    b.card ≤ sizeCutoff F hUnbounded a.card := by
  exact G.minimal_growth_extension_card_le F
    (sizeCutoff F hUnbounded)
    (sizeCutoff_inverse_property F hMono hUnbounded)
    a b hMin hGrowth x hxb hxna

end CFGrowthNumerics
end BigHrushovski
