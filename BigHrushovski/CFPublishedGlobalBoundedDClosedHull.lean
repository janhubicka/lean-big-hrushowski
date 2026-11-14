import BigHrushovski.CFGlobalBoundedDClosedHull
import BigHrushovski.CFPublishedFiniteGenericity

/-!
# Bounded d-closure under the manuscript's published F

The general theorem in CFGlobalBoundedDClosedHull works with the
restriction F : Nat → Real. Here we derive that restriction's monotonicity
and unboundedness from the published F : Real≥0 → Real≥0 and state the
exact manuscript conclusion on an arbitrary graph carrier.

We name the generalized-inverse bound by its defining equivalence,
rather than by a separately supplied inverse function. This removes
the representation mismatch between the paper and Lean.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics

/-- Any graph all of whose finite induced subgraphs belong to the
published growth class has least globally strictly d-closed finite
hulls. The cardinality bound is exactly the greatest integer K with
F(K) ≤ 2|s|, including flat intervals of F.

No countability, pre-existing finite d-closed chain, genericity or
free-amalgamation hypothesis is needed once the finite age bound holds.
-/
theorem publishedGrowth_exists_least_bounded_globalDClosed_hull
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    {V : Type*} [DecidableEq V]
    (G : GraphOn V)
    (hAge : ∀ u : Finset V,
      publishedCardinalGrowth F u.card ≤ (G.predim u : ℝ))
    (s : Finset V) :
    ∃ K : ℕ,
      (∀ n : ℕ,
        publishedCardinalGrowth F n ≤ 2 * (s.card : ℝ) ↔ n ≤ K) ∧
      ∃ h : Finset V,
        s ⊆ h ∧ G.toPredimension.IsGloballyDClosed h ∧
        h.card ≤ K ∧
        ∀ t : Finset V, s ⊆ t →
          G.toPredimension.IsGloballyDClosed t → h ⊆ t := by
  let R : ℝ → ℝ := extendPublishedGrowth F
  let Fn : ℕ → ℝ := fun n => R (n : ℝ)
  have hFnEq : Fn = publishedCardinalGrowth F := by
    funext n
    exact extendPublishedGrowth_nat F n
  have hFnZero : Fn 0 = 0 := by
    simpa only [Fn, R, Nat.cast_zero] using
      (extendPublishedGrowth_zero F hZero)
  have hFnMono : Monotone Fn :=
    realGrowth_nat_monotone R (extendPublishedGrowth_monotone F hMono)
  have hFnUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < Fn n :=
    realGrowth_nat_unbounded R
      (extendPublishedGrowth_monotone F hMono)
      (extendPublishedGrowth_unbounded F hUnbounded)
  have hFnAge : ∀ u : Finset V,
      Fn u.card ≤ (G.predim u : ℝ) := by
    intro u
    rw [hFnEq]
    exact hAge u
  let K : ℕ := growthInverseAt Fn hFnUnbounded (2 * (s.card : ℝ))
  refine ⟨K, ?_, ?_⟩
  · intro n
    rw [← hFnEq]
    exact growthInverseAt_iff Fn hFnZero hFnMono hFnUnbounded
      (2 * (s.card : ℝ)) (by positivity) n
  · obtain ⟨h, hs, hGlobal, hSize, hLeast⟩ :=
      G.exists_least_bounded_globalDClosed_hull
        Fn hFnMono hFnUnbounded hFnAge s
    exact ⟨h, hs, hGlobal, hSize, hLeast⟩

end CFCoherentTower
end BigHrushovski
