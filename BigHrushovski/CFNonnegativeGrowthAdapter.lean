import BigHrushovski.CFRealGrowthRestriction

/-!
# Growth functions on the published nonnegative real domain

The manuscript assumes F : ℝ≥0 → ℝ≥0, whereas the existing
finite-response theorem uses a monotone unbounded function ℝ → ℝ.
There is no mathematical reason to introduce negative arguments:
extend F constantly below zero. This file makes that choice explicit.

We represent the nonnegative reals as an ordered real subtype rather
than suppressing the domain restriction. Input and output nonnegativity
are then part of the type. Restriction to natural-number cardinalities
is **exact**, not merely asymptotic. Continuity is not used in the
finite growth-size estimates.
-/

namespace BigHrushovski
namespace CFGrowthNumerics

/-- The nonnegative reals, with the inherited order. -/
abbrev NonnegativeReal := {x : ℝ // 0 ≤ x}

/-- Published-domain growth functions have nonnegative values and
are only defined on nonnegative real arguments. -/
abbrev PublishedGrowth := NonnegativeReal → NonnegativeReal

/-- Extend a growth function constantly to negative arguments. -/
def extendPublishedGrowth (F : PublishedGrowth) (x : ℝ) : ℝ :=
  (F ⟨max x 0, le_max_right x 0⟩).val

/-- The real-domain extension remains nonnegative everywhere. -/
theorem extendPublishedGrowth_nonneg (F : PublishedGrowth) (x : ℝ) :
    0 ≤ extendPublishedGrowth F x :=
  (F ⟨max x 0, le_max_right x 0⟩).property

/-- The extension agrees literally with F on every nonnegative
input; in particular it agrees at every finite cardinality. -/
theorem extendPublishedGrowth_agrees (F : PublishedGrowth)
    (x : NonnegativeReal) :
    extendPublishedGrowth F x.val = (F x).val := by
  simp [extendPublishedGrowth, max_eq_left x.property]

theorem extendPublishedGrowth_nat (F : PublishedGrowth) (n : ℕ) :
    extendPublishedGrowth F (n : ℝ) =
      (F ⟨(n : ℝ), Nat.cast_nonneg n⟩).val := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simp [extendPublishedGrowth, max_eq_left hn]

/-- Nondecreasing growth on the nonnegative domain gives
a nondecreasing extension over all real arguments. -/
theorem extendPublishedGrowth_monotone (F : PublishedGrowth)
    (hMono : Monotone F) :
    Monotone (extendPublishedGrowth F) := by
  intro x y hxy
  have hmax : max x 0 ≤ max y 0 :=
    max_le_max hxy (le_refl (0 : ℝ))
  have hxy' :
      (⟨max x 0, le_max_right x 0⟩ : NonnegativeReal) ≤
        (⟨max y 0, le_max_right y 0⟩ : NonnegativeReal) := hmax
  exact hMono hxy'

/-- Unboundedness of the published growth function supplies the
real-domain unboundedness used by the exact inverse K. -/
theorem extendPublishedGrowth_unbounded (F : PublishedGrowth)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val) :
    ∀ t : ℝ, ∃ x : ℝ, t < extendPublishedGrowth F x := by
  intro t
  obtain ⟨x, hx⟩ := hUnbounded t
  refine ⟨x.val, ?_⟩
  simpa [extendPublishedGrowth, max_eq_left x.property] using hx

/-- The published condition F(0)=0 is the exact real-domain zero
condition needed by the already verified numerical inverse. -/
theorem extendPublishedGrowth_zero (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0) :
    extendPublishedGrowth F 0 = 0 := by
  simpa [extendPublishedGrowth] using hZero

end CFGrowthNumerics
end BigHrushovski
