import BigHrushovski.CFDClosedFiniteSubtype
import BigHrushovski.CFRealBirthRecognition

/-!
# Empty-base strict d-closedness from finite C_F membership

The manuscript assumes that the empty substructure is d-closed
in every finite member of C_F. It is unnecessary to impose
a second independent global empty-base hypothesis on a
countable comparison graph that satisfies the complete
finite growth inequality: each of its finite induced graphs
belongs to C_F, and the finite empty-base assumption applies
to every one of them.

The proof uses the exact finite induced-subtype restriction
already verified in CF DClosedFiniteSubtype and hence transports
*strict* predimension inequalities, not merely strongness.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- The paper's independent finite empty-base hypothesis,
expressed for every finite growth-class graph. This does not
follow from monotonicity of the growth function. -/
def HasClassDClosedEmpty (F : ℕ → ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : GraphOn V),
      G.IsGrowthSparse F (Finset.univ : Finset V) →
      G.toPredimension.IsDClosed ∅ Finset.univ

/-- Every countable graph satisfying all finite C_F growth
inequalities has globally strictly d-closed empty base,
provided the paper's independent empty-base class assumption
holds. No finite closed-cover or genericity assumption is used. -/
theorem empty_globalDClosed_of_growth_and_class
    (F : ℕ → ℝ) (N : GraphOn ℕ)
    (hGrowth : HasGrowthInequality F N)
    (hEmpty : HasClassDClosedEmpty F) :
    N.toPredimension.IsGloballyDClosed ∅ := by
  classical
  intro b hb hne
  have hSparse : N.IsGrowthSparse F b := by
    intro s _
    exact hGrowth s
  let H : GraphOn (CFDClosedFiniteSubtype.Carrier b) :=
    CFDClosedFiniteSubtype.graph N b
  have hSparseH : H.IsGrowthSparse F Finset.univ :=
    (CFDClosedFiniteSubtype.growthSparse_iff N F b).mp hSparse
  have hBaseEmpty :
      CFDClosedFiniteSubtype.base b ∅ =
        (∅ : Finset (CFDClosedFiniteSubtype.Carrier b)) := by
    simp [CFDClosedFiniteSubtype.base]
  have hLocal : H.toPredimension.IsDClosed
      (CFDClosedFiniteSubtype.base b ∅) Finset.univ := by
    rw [hBaseEmpty]
    exact hEmpty (CFDClosedFiniteSubtype.Carrier b) H hSparseH
  have hRelative : N.toPredimension.IsDClosed ∅ b :=
    (CFDClosedFiniteSubtype.dClosed_iff N ∅ b
      (Finset.empty_subset b)).mpr hLocal
  exact hRelative.2 b hb hne (Finset.Subset.refl b)

/-- The same finite class assumption discharges the empty-base
premise in recognition of the original canonical C_F birth graph.
Only the comparison graph's growth, finite closed covers and
complete strict induced finite-extension responses remain. -/
theorem realBirth_unique_without_comparison_empty
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : CFCoherentTower.HasFiniteClassDClosedFreeJoins
      (CFGrowthNumerics.cardinalGrowth F))
    (hRequests : ∀ n : ℕ,
      Nonempty (CFStageCatalogue.StageRequest
        (CFCoherentTower.stage
          (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) n).graph
        (CFStageCatalogue.GrowthAllowedLocal (CFGrowthNumerics.cardinalGrowth F))
        (fun P =>
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) P.card)))
    (N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality
      (CFGrowthNumerics.cardinalGrowth F) N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hResponsesN : HasFiniteDClosedIntervalResponses
      (CFGrowthNumerics.cardinalGrowth F) N)
    (hEmptyClass : HasClassDClosedEmpty
      (CFGrowthNumerics.cardinalGrowth F)) :
    ∃ φ : CFCoherentTower.RealBirthVertex F hMono hUnbounded ≃ ℕ,
      ∀ x y : CFCoherentTower.RealBirthVertex F hMono hUnbounded,
        (CFCoherentTower.realCountableGraph F hMono hUnbounded).adj x y ↔
          N.adj (φ x) (φ y) := by
  exact CFCoherentTower.realCountableGraph_unique_of_requests
    F hZero hMono hUnbounded hFree hRequests N
    hGrowthN hCoverN hResponsesN
    (empty_globalDClosed_of_growth_and_class
      (CFGrowthNumerics.cardinalGrowth F) N hGrowthN hEmptyClass)

end CFDClosedBackAndForth
end BigHrushovski
