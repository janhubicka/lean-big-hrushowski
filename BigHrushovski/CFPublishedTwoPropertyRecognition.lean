import BigHrushovski.CFPublishedFraisseRecognition
import BigHrushovski.CFPublishedGlobalBoundedDClosedHull
import BigHrushovski.CFStandardFraisseExtension
import BigHrushovski.CFFraisseThreeData

/-!
# Recognising the C_F generic from two finite properties

The earlier recognition interface asks a countably infinite comparison
graph for three pieces of finite data: growth, globally strict d-closed
finite covers, and all prescribed finite strict d-closed extensions.

The general bounded d-closure theorem makes the covering condition
redundant. A monotone unbounded growth bound, together with the growth
inequality on every finite induced subgraph, supplies a finite globally
strictly d-closed hull for each finite set.

Thus the two substantive genericity properties are precisely the finite
growth age and the literal prescribed finite strong extension property.
The comparison carrier must still be countably infinite, and the
manuscript's independent strict empty-base class assumption is retained
to start strict back-and-forth at the empty map.

No functional (R,H) homogeneity or level-lifting conclusion is claimed.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

open CFGrowthNumerics

/-- The finite globally strictly d-closed cover hypothesis is
automatic in a graph whose finite subsets satisfy a monotone
unbounded growth inequality. There is no countability assumption
in the underlying bounded-hull theorem. -/
theorem finiteDClosedCovers_of_growth
    (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (G : GraphOn ℕ)
    (hGrowth : HasGrowthInequality F G) :
    HasFiniteDClosedCovers G := by
  intro s
  obtain ⟨h, hs, hGlobal, _, _⟩ :=
    G.exists_least_bounded_globalDClosed_hull
      F hMono hUnbounded hGrowth s
  exact ⟨h, hs, hGlobal⟩

/-- Under monotone unbounded growth, the old three-property strict
genericity criterion follows from just finite age and the complete
prescribed finite extension property. It does not require an
independently supplied finite strong-cover axiom. -/
theorem finiteFraisseData_of_growth_extensions
    (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (G : GraphOn ℕ)
    (hGrowth : HasGrowthInequality F G)
    (hExtensions : HasFiniteDClosedIntervalResponses F G) :
    HasFiniteFraisseData F G :=
  ⟨hGrowth, finiteDClosedCovers_of_growth
    F hMono hUnbounded G hGrowth, hExtensions⟩

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The published growth assumptions and the finite age inequality
supply globally strictly d-closed finite covers on an arbitrary
vertex carrier, without a pre-existing strong chain or genericity. -/
theorem publishedGrowth_hasFiniteDClosedCovers
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    {V : Type*} [DecidableEq V]
    (G : GraphOn V)
    (hGrowth : ∀ u : Finset V,
      publishedCardinalGrowth F u.card ≤ (G.predim u : ℝ)) :
    ∀ s : Finset V,
      ∃ c : Finset V,
        s ⊆ c ∧ G.toPredimension.IsGloballyDClosed c := by
  intro s
  obtain ⟨K, hInv, c, hs, hc, hCard, hLeast⟩ :=
    publishedGrowth_exists_least_bounded_globalDClosed_hull
      F hZero hMono hUnbounded G hGrowth s
  exact ⟨c, hs, hc⟩

/-- Two-property strong Fraisse recognition for the actual published
C_F construction. The countably infinite comparison graph needs
only (1) the full finite growth inequality and (2) every prescribed
induced finite strict d-closed extension.

In particular, neither a covering finite d-closed chain nor a
separately assumed global strict cover property appears in this
statement. Those covers follow from published bounded d-closure.

The strictly d-closed empty-base class condition and singleton
membership remain separate hypotheses on C_F: they are not inferred
from monotonicity, unboundedness, or the extension property. -/
theorem publishedBirth_iso_of_growth_and_extensions
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
    {V : Type*} [DecidableEq V]
    (G : GraphOn V)
    (enumerate : ℕ ≃ V)
    (hGrowth : ∀ s : Finset V,
      publishedCardinalGrowth F s.card ≤ (G.predim s : ℝ))
    (hExtensions : HasStandardFiniteDClosedExtensions
      (publishedCardinalGrowth F) G) :
    ∃ φ : PublishedBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  classical
  let R : ℝ → ℝ := extendPublishedGrowth F
  have hFnEq :
      (fun n : ℕ => R (n : ℝ)) = publishedCardinalGrowth F := by
    funext n
    exact extendPublishedGrowth_nat F n
  have hMonoNat : Monotone (publishedCardinalGrowth F) := by
    rw [← hFnEq]
    exact realGrowth_nat_monotone R
      (extendPublishedGrowth_monotone F hMono)
  have hUnboundedNat :
      ∀ t : ℝ, ∃ n : ℕ, t < publishedCardinalGrowth F n := by
    rw [← hFnEq]
    exact realGrowth_nat_unbounded R
      (extendPublishedGrowth_monotone F hMono)
      (extendPublishedGrowth_unbounded F hUnbounded)
  have hGrowthNat :
      HasGrowthInequality (publishedCardinalGrowth F)
        (G.pullback enumerate) :=
    G.finiteGrowth_pullback enumerate (publishedCardinalGrowth F)
      hGrowth
  have hResponsesNat :
      HasFiniteDClosedIntervalResponses (publishedCardinalGrowth F)
        (G.pullback enumerate) :=
    HasFiniteDClosedResponsesOn.pullback
      (publishedCardinalGrowth F) G enumerate
      (hExtensions.toNatIntervals (publishedCardinalGrowth F) G)
  have hFiniteNat :
      HasFiniteFraisseData (publishedCardinalGrowth F)
        (G.pullback enumerate) :=
    finiteFraisseData_of_growth_extensions
      (publishedCardinalGrowth F) hMonoNat hUnboundedNat
      (G.pullback enumerate) hGrowthNat hResponsesNat
  have hEmptyFinite :
      HasClassDClosedEmpty (publishedCardinalGrowth F) := by
    intro W _ _ B hB
    exact hEmptyClass W B hB
  let hGeneric : PresentedStrictGeneric
      (publishedCardinalGrowth F) G :=
    {
      enumerate := enumerate
      finite_data := hFiniteNat.toStrictGenericity
        (publishedCardinalGrowth F) (G.pullback enumerate)
        hEmptyFinite
    }
  exact publishedBirth_iso_presentedStrictGeneric
    F hZero hMono hUnbounded hFree hEmptyClass hSingleton
    G hGeneric

end CFCoherentTower
end BigHrushovski
