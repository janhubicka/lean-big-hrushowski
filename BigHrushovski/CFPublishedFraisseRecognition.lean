import BigHrushovski.CFPublishedBirthGenericity
import BigHrushovski.CFPresentedStrictGeneric

/-!
# The actual C_F birth graph and the published countable strong generic

This is the final comparison interface: the growth function has
exactly the nonnegative domain and codomain used in the manuscript,
and the comparison structure is on an arbitrary countably infinite
carrier with its own vertex names, not necessarily on ℕ.

Under the printed free-amalgamation, singleton and empty-base
hypotheses, the literal singleton stage-request construction yields
an infinite birth carrier and the full strict d-closed finite
extension property. The comparison graph is required to have the
defining four finite properties of the strong C_F Fraisse generic,
not a pre-existing isomorphism with the birth graph.

The only manuscript-facing task remaining after this theorem is
to identify the already denoted M_F with such a comparison generic
via its Fraisse-limit characterization; no new ad hoc numerical or
stage-existence hypothesis appears in the theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- Under the printed finite C_F assumptions, the canonical
birth-labelled graph is induced-isomorphic to any presented
countable strong C_F generic on its **original** vertex type.
This does not assume the desired graph isomorphism.

The numerical singleton inequality is exactly the one-vertex
growth-class condition F(1) ≤ δ({v}) = 2. -/
theorem publishedBirth_iso_presentedStrictGeneric
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2)
    {V : Type*} (G : GraphOn V)
    (hGeneric : PresentedStrictGeneric (publishedCardinalGrowth F) G) :
    ∃ φ : PublishedBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  obtain ⟨ψ, hψ⟩ :=
    publishedBirth_unique_of_growthClassAssumptions
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton
      (G.pullback hGeneric.enumerate)
      hGeneric.finite_data.growth
      hGeneric.finite_data.finite_closed_covers
      hGeneric.finite_data.finite_extensions
      hGeneric.finite_data.empty_closed
  refine ⟨ψ.trans hGeneric.enumerate, ?_⟩
  intro x y
  change (publishedCountableGraph F hMono hUnbounded).adj x y ↔
    (G.pullback hGeneric.enumerate).adj (ψ x) (ψ y)
  exact hψ x y

end CFCoherentTower
end BigHrushovski
