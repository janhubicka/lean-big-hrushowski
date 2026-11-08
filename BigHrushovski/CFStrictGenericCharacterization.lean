import BigHrushovski.CFRealBirthRecognition
import BigHrushovski.CFPublishedNatRecognition

/-!
# The countable strict C_F generic: a finite recognition criterion

We package the four finite properties characterizing the countable
strong Fraisse limit of C_F graphs. The extension property is
*induced*, with a literally prescribed old map and globally strictly
d-closed image; weak strongness or a merely graph-homomorphic
response does not suffice.

This criterion applies to a graph already presented on ℕ.
It does not assert that an arbitrary countable graph is generic,
nor introduce an unverified named `M_F` constant.

The proof of uniqueness is the previously verified strict
d-closed back-and-forth theorem. In particular, no new
infinite construction or independent extension lemma is needed.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- The four finite recognition properties of a countable strict
C_F generic, with its actual vertices labelled by ℕ.

They include (i) all finite C_F growth inequalities;
(ii) finite globally strictly d-closed covers;
(iii) complete prescribed-base induced finite d-closed extension
responses; (iv) global strict d-closedness of the empty set. -/
structure HasCountableStrictGenericity
    (F : ℕ → ℝ) (G : GraphOn ℕ) : Prop where
  growth : HasGrowthInequality F G
  finite_closed_covers : HasFiniteDClosedCovers G
  finite_extensions : HasFiniteDClosedIntervalResponses F G
  empty_closed : G.toPredimension.IsGloballyDClosed ∅

/-- The countable strict C_F generic is unique up to an
induced graph isomorphism. Both adjacency and nonadjacency
are preserved and reflected. -/
theorem unique_of_strictGenericity
    (F : ℕ → ℝ) (G H : GraphOn ℕ)
    (hG : HasCountableStrictGenericity F G)
    (hH : HasCountableStrictGenericity F H) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      G.adj x y ↔ H.adj (e x) (e y) :=
  exists_induced_equiv_of_finiteDClosedResponses
    F G H hG.growth hH.growth
    hG.finite_closed_covers hH.finite_closed_covers
    hG.finite_extensions hH.finite_extensions
    hG.empty_closed hH.empty_closed

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- The genuine Nat presentation of the canonical C_F birth graph
satisfies the full strict genericity criterion, conditional only
on the already required class-level free-join property and a
genuine Nat equivalence of the birth carrier. -/
theorem realCountableGraphNat_hasStrictGenericity
    (F : ℝ → ℝ) (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (ι : ℕ ≃ RealBirthVertex F hMono hUnbounded) :
    HasCountableStrictGenericity (cardinalGrowth F)
      (realCountableGraphNat F hMono hUnbounded ι) := by
  obtain ⟨hg, hc, hr, he⟩ :=
    realCountableGraphNat_genericData F hZero hMono
      hUnbounded hFree ι
  exact ⟨hg, hc, hr, he⟩

/-- The actual tagged birth graph is isomorphic to every
countable strict C_F generic, once the construction has a
permitted finite request at every stage.

The comparison hypothesis is a single named finite criterion
rather than four anonymous assumptions. -/
theorem realBirth_unique_of_requests_hasStrictGenericity
    (F : ℝ → ℝ) (hZero : F 0 = 0)
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
    (hN : HasCountableStrictGenericity (cardinalGrowth F) N) :
    ∃ φ : RealBirthVertex F hMono hUnbounded ≃ ℕ,
      ∀ x y : RealBirthVertex F hMono hUnbounded,
        (realCountableGraph F hMono hUnbounded).adj x y ↔
          N.adj (φ x) (φ y) :=
  realCountableGraph_unique_of_requests
    F hZero hMono hUnbounded hFree hRequests N
    hN.growth hN.finite_closed_covers
    hN.finite_extensions hN.empty_closed

end CFCoherentTower
end BigHrushovski
