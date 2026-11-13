import BigHrushovski.CFPublishedOwnFraissePresentation
import BigHrushovski.CFGrowthClass

/-!
# Exact strong age of the published C_F birth graph

Lemma 3.14 of the big Hrushovski manuscript identifies the graph reduct
of the canonical birth construction with the strong Fraisse limit M_F.
The two directions of the finite-age assertion had previously been
certified separately: every induced finite birth subgraph belongs to
C_F, and every finite C_F-member has a globally strictly d-closed
induced copy in the birth graph.

This file records their exact equivalence. In the reverse direction,
an induced injection suffices for age membership, while the forward
direction supplies a strictly d-closed image. The proof uses no
comparison model and no assumption that the desired isomorphism exists.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- A finite graph belongs to the published growth class if and only
if it has an induced globally strictly d-closed copy in the actual
canonical birth graph. This is the two-sided *strong* age assertion,
on an arbitrary finite carrier with its original vertex labels.

The right-to-left implication only needs inducedness; the extra
strict closure in the conclusion is genuinely supplied by the
left-to-right direction. -/
theorem publishedBirth_exactStrongAge
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass
      (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2)
    (W : Type) [Fintype W] [DecidableEq W]
    (B : GraphOn W) :
    B.IsGrowthSparse (publishedCardinalGrowth F)
      (Finset.univ : Finset W) ↔
      ∃ g : W → PublishedBirthVertex F hMono hUnbounded,
        Function.Injective g ∧
        (∀ x y : W,
          B.adj x y ↔
            (publishedCountableGraph F hMono hUnbounded).adj
              (g x) (g y)) ∧
        (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
          ((Finset.univ : Finset W).image g) := by
  classical
  constructor
  · intro hGrowth
    exact publishedBirth_finiteStrongUniversality
      F hZero hMono hUnbounded hEmptyClass W B hGrowth
  · rintro ⟨g, hgInj, hgAdj, _⟩
    have hAge := (publishedBirth_standardStrongFraisseLimitPresentation
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton).age
    have hImageGrowth :
        (publishedCountableGraph F hMono hUnbounded).IsGrowthSparse
          (publishedCardinalGrowth F)
          ((Finset.univ : Finset W).image g) := by
      intro s _
      exact hAge s
    exact (B.growthSparse_image_iff
      (publishedCountableGraph F hMono hUnbounded)
      (publishedCardinalGrowth F) g hgInj hgAdj
      (Finset.univ : Finset W)).mp hImageGrowth

end CFCoherentTower
end BigHrushovski
