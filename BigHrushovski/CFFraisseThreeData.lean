import BigHrushovski.CFEmptyBaseTransfer
import BigHrushovski.CFStrictGenericCharacterization
import BigHrushovski.CFPresentedStrictGeneric

/-!
# A three-part finite recognition criterion for the strong C_F limit

Under the paper's standing assumption that the empty substructure
is strictly d-closed in every finite member of C_F, the countable
generic's empty-base property is redundant: it follows from
membership of every finite induced subgraph in C_F.

A countably infinite comparison generic can therefore be specified
by precisely three finite properties: growth-class membership,
finite globally strictly d-closed covers, and the complete
prescribed finite strictly d-closed extension property. A genuine
enumeration is still needed to represent an arbitrary carrier on ℕ.

No isomorphism with the canonical birth graph is assumed in the
definition. Uniqueness follows by reusing the kernel-verified
four-part criterion together with the independently checked
finite-to-global empty-base transfer.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- Three finite properties of a countable strict C_F generic,
without separately postulating global strict d-closedness of
the empty set. The omitted property follows from the paper's
independent finite-class empty-base hypothesis. -/
structure HasFiniteFraisseData
    (F : ℕ → ℝ) (G : GraphOn ℕ) : Prop where
  growth : HasGrowthInequality F G
  finite_closed_covers : HasFiniteDClosedCovers G
  finite_extensions : HasFiniteDClosedIntervalResponses F G

/-- The manuscript's finite empty-base class condition upgrades
the three independently checkable finite properties to the exact
four-part strict countable genericity criterion. -/
theorem HasFiniteFraisseData.toStrictGenericity
    (F : ℕ → ℝ) (G : GraphOn ℕ)
    (h : HasFiniteFraisseData F G)
    (hEmptyClass : HasClassDClosedEmpty F) :
    HasCountableStrictGenericity F G :=
  ⟨h.growth, h.finite_closed_covers, h.finite_extensions,
    empty_globalDClosed_of_growth_and_class F G h.growth hEmptyClass⟩

/-- A countable strict C_F generic on its original vertex carrier,
specified only by an enumeration and the three finite data. It
does not contain a desired graph isomorphism as a field. -/
structure PresentedFraisseData
    (F : ℕ → ℝ) {V : Type*} (G : GraphOn V) where
  enumerate : ℕ ≃ V
  finite_data : HasFiniteFraisseData F (G.pullback enumerate)

/-- Recover the complete four-part presentation without any
extra property of the countable comparison graph. -/
def PresentedFraisseData.toPresentedStrictGeneric
    (F : ℕ → ℝ) {V : Type*} (G : GraphOn V)
    (h : PresentedFraisseData F G)
    (hEmptyClass : HasClassDClosedEmpty F) :
    PresentedStrictGeneric F G where
  enumerate := h.enumerate
  finite_data :=
    h.finite_data.toStrictGenericity F (G.pullback h.enumerate) hEmptyClass

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- Under the independently stated finite empty-base class
condition, the canonical C_F birth graph is induced-isomorphic
to any presented countable comparison generic specified by the
three finite Fraisse recognition properties. -/
theorem realBirth_iso_presentedFraisseData
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hRequests : ∀ n : ℕ,
      Nonempty (CFStageCatalogue.StageRequest
        (stage (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) n).graph
        (CFStageCatalogue.GrowthAllowedLocal (cardinalGrowth F))
        (fun P => (cardinalGrowthBound F hMono hUnbounded) P.card)))
    {V : Type*} (G : GraphOn V)
    (hFraisse : PresentedFraisseData (cardinalGrowth F) G)
    (hEmptyClass : HasClassDClosedEmpty (cardinalGrowth F)) :
    ∃ φ : RealBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : RealBirthVertex F hMono hUnbounded,
        (realCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  exact realBirth_iso_presentedStrictGeneric F hZero hMono
    hUnbounded hFree hRequests G
    (hFraisse.toPresentedStrictGeneric
      (cardinalGrowth F) G hEmptyClass)

end CFCoherentTower
end BigHrushovski
