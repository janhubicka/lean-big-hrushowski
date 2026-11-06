import BigHrushovski.CFBirthInfinitude
import BigHrushovski.CFRealNatRecognition

/-!
# Strict C_F generic recognition on the actual birth-labelled carrier

The countable birth graph carries a genuinely different vertex
type from the Nat-based strict genericity theorem. The verified
nonempty-request criterion gives infinitude, and together with
the verified countability of birth vertices supplies a real
equivalence with ℕ.

Compose this equivalence with the Nat-generic recognition theorem.
The resulting induced graph equivalence is on the *original*
birth-labelled carrier, not on an artificial supergraph or
a quotient with extra vertices. This is a conditional version
of the manuscript's M_F^dagger identification: the paper's
singleton/empty-base hypotheses must still supply the actual
nonempty request at every level, and the comparison graph
has to satisfy the usual finite strict genericity properties.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The actual countable C_F birth-labelled graph is induced-isomorphic
to every countable Nat-carrier graph with the same growth inequality,
finite globally strict d-closed covers, complete finite d-closed
extension responses and globally d-closed empty base, **provided**
there is an actual request at every birth level.

No embedding monoid, finite unique level lifting, or orientation
expansion is used or claimed. -/
theorem realCountableGraph_unique_of_requests
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
    (N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality (cardinalGrowth F) N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hResponsesN : HasFiniteDClosedIntervalResponses
      (cardinalGrowth F) N)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ φ : RealBirthVertex F hMono hUnbounded ≃ ℕ,
      ∀ x y : RealBirthVertex F hMono hUnbounded,
        (realCountableGraph F hMono hUnbounded).adj x y ↔
          N.adj (φ x) (φ y) := by
  let ι : ℕ ≃ RealBirthVertex F hMono hUnbounded :=
    natEquivBirth_of_requests
      (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) hRequests
  obtain ⟨e, he⟩ :=
    realCountableGraphNat_unique_against
      F hZero hMono hUnbounded hFree ι N
      hGrowthN hCoverN hResponsesN hEmptyN
  refine ⟨ι.symm.trans e, ?_⟩
  intro x y
  have h := he (ι.symm x) (ι.symm y)
  change (realCountableGraph F hMono hUnbounded).adj
      (ι (ι.symm x)) (ι (ι.symm y)) ↔
      N.adj (e (ι.symm x)) (e (ι.symm y)) at h
  simpa [Equiv.trans_apply] using h

end CFCoherentTower
end BigHrushovski
