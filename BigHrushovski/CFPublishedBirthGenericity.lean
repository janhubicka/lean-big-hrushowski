import BigHrushovski.CFSingletonStageCoverage
import BigHrushovski.CFPublishedFiniteGenericity

/-!
# Exact published-domain C_F birth generic recognition

The manuscript takes F on nonnegative real inputs with nonnegative
outputs, and assumes F(0)=0, monotonicity, unboundedness, one-vertex
membership and strict d-closedness of the empty base in every member.
The free-amalgamation property of the restricted finite class is
an independent standing hypothesis.

We use the certified constant-below-zero extension to specialize the
real-growth singleton coverage and actual birth-graph recognition
theorem. Every growth inequality is tested on the *exact* original
finite cardinality restriction. No extra cutoff, stage request or
unexplained extension to negative real inputs appears.

The final identification is with any countable comparison graph
satisfying all four strict genericity conditions, not an assumption
that the desired isomorphism already exists.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The countable birth-labelled C_F graph is the unique countable
strict d-closed generic under the numerical and finite class
hypotheses of the printed manuscript, relative to a comparison
graph satisfying the usual complete finite extension properties.

The exact F(1)≤2 hypothesis is the one-vertex class-membership
condition expressed numerically for δ({v})=2. -/
theorem publishedBirth_unique_of_growthClassAssumptions
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2)
    (N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality (publishedCardinalGrowth F) N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hResponsesN : HasFiniteDClosedIntervalResponses
      (publishedCardinalGrowth F) N)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ φ : PublishedBirthVertex F hMono hUnbounded ≃ ℕ,
      ∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          N.adj (φ x) (φ y) := by
  have hFreeReal :
      HasFiniteClassDClosedFreeJoins
        (cardinalGrowth (extendPublishedGrowth F)) := by
    simpa only [publishedCardinalGrowth_eq F] using hFree
  have hEmptyReal :
      EmptyDClosedInGrowthClass
        (cardinalGrowth (extendPublishedGrowth F)) := by
    simpa only [publishedCardinalGrowth_eq F] using hEmptyClass
  have hGrowthReal :
      HasGrowthInequality
        (cardinalGrowth (extendPublishedGrowth F)) N := by
    simpa only [publishedCardinalGrowth_eq F] using hGrowthN
  have hResponsesReal :
      HasFiniteDClosedIntervalResponses
        (cardinalGrowth (extendPublishedGrowth F)) N := by
    simpa only [publishedCardinalGrowth_eq F] using hResponsesN
  have hSingletonReal :
      extendPublishedGrowth F 1 ≤ 2 := by
    simpa [extendPublishedGrowth] using hSingleton
  exact realBirth_unique_of_growthClassAssumptions
    (extendPublishedGrowth F)
    (extendPublishedGrowth_zero F hZero)
    (extendPublishedGrowth_monotone F hMono)
    (extendPublishedGrowth_unbounded F hUnbounded)
    hFreeReal hEmptyReal hSingletonReal
    N hGrowthReal hCoverN hResponsesReal hEmptyN

end CFCoherentTower
end BigHrushovski
