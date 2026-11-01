import BigHrushovski.CFRealNatRecognition
import BigHrushovski.CFPublishedFiniteGenericity

/-!
# Countable strict C_F genericity under the published growth hypotheses

The manuscript's growth function is defined on nonnegative reals,
with nonnegative values. Its exact canonical extension to ℝ has
already been formalized and shown to have the same values on all
integer vertex cardinalities.

This module specializes the verified countable Nat generic
recognition theorem to that published domain. It adds no
analytic assumptions or externally chosen inverse bound.

The genuine equivalence between ℕ and the birth carrier, and
the finite genericity data of a comparison graph, remain visible.
Their construction is not hidden in the numerical adapter.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- Countable strict generic uniqueness with exactly the published
nonnegative-domain function F. The target graph on ℕ must still
satisfy the full finite growth, cover, extension and empty-base
recognition hypotheses. -/
theorem publishedCountableGraphNat_unique_against
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : CFCoherentTower.HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (ι : ℕ ≃ PublishedBirthVertex F hMono hUnbounded)
    (N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality (publishedCardinalGrowth F) N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hResponsesN : HasFiniteDClosedIntervalResponses
      (publishedCardinalGrowth F) N)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      ((publishedCountableGraph F hMono hUnbounded).pullback ι).adj x y ↔
        N.adj (e x) (e y) := by
  have hFreeReal : HasFiniteClassDClosedFreeJoins
      (cardinalGrowth (extendPublishedGrowth F)) := by
    simpa only [publishedCardinalGrowth_eq F] using hFree
  have hGrowthReal : HasGrowthInequality
      (cardinalGrowth (extendPublishedGrowth F)) N := by
    simpa only [publishedCardinalGrowth_eq F] using hGrowthN
  have hResponsesReal : HasFiniteDClosedIntervalResponses
      (cardinalGrowth (extendPublishedGrowth F)) N := by
    simpa only [publishedCardinalGrowth_eq F] using hResponsesN
  exact realCountableGraphNat_unique_against
    (extendPublishedGrowth F)
    (extendPublishedGrowth_zero F hZero)
    (extendPublishedGrowth_monotone F hMono)
    (extendPublishedGrowth_unbounded F hUnbounded)
    hFreeReal ι N hGrowthReal hCoverN hResponsesReal hEmptyN

end CFCoherentTower
end BigHrushovski
