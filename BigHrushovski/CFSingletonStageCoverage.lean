import BigHrushovski.CFSingletonStageRequest
import BigHrushovski.CFRealGenericCertificate
import BigHrushovski.CFRealBirthRecognition

/-!
# A singleton request at every C_F stage from the published class assumptions

The manuscript assumes both that the one-vertex graph belongs to C_F
and that the empty graph is strictly d-closed in every finite member.
These are independent assumptions, not consequences of F(0)=0,
monotonicity or unboundedness.

This module combines those class hypotheses with the proved growth
membership of the actual finite stages and the exact numerical inverse.
It produces a *literal* singleton StageRequest at every stage, not
merely some abstract nonempty local extension.

The proof requires the finite singleton-request construction from the
parent PR. The countable conditional birth-graph recognition is already
kernel-checked on main; no countable isomorphism is presupposed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFStageCatalogue

/-- The exact paper assumption that the empty support is strictly
d-closed in every finite member of the restricted growth class. -/
def EmptyDClosedInGrowthClass (F : ℕ → ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : GraphOn V),
      G.IsGrowthSparse F (Finset.univ : Finset V) →
      G.toPredimension.IsDClosed ∅ Finset.univ

/-- Every canonical finite stage has an actual permitted singleton
request, under the paper's restricted free-amalgamation, empty-base
and singleton growth assumptions.

The bound on one fresh vertex is derived from the *exact* inverse,
not separately assumed. The empty-base property is applied to each
stage only after its C_F class membership has been proved. -/
theorem singletonRequest_every_realStage
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2) :
    ∀ n : ℕ,
      Nonempty (StageRequest
        (stage (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) n).graph
        (GrowthAllowedLocal (cardinalGrowth F))
        (fun P => (cardinalGrowthBound F hMono hUnbounded) P.card)) := by
  classical
  let Fnat : ℕ → ℝ := cardinalGrowth F
  let K : ℕ → ℕ := cardinalGrowthBound F hMono hUnbounded
  have hStageFree : ∀ n,
      (stage Fnat K (n + 1)).graph.GrowthClosedUnderDClosedFreeJoins Fnat := by
    intro n
    exact hFree (stage Fnat K (n + 1)).carrier
      (stage Fnat K (n + 1)).graph
  have hStageGrowth : ∀ n,
      (stage Fnat K n).graph.IsGrowthSparse Fnat
        (Finset.univ : Finset (stage Fnat K n).carrier) :=
    all_stages_growth Fnat K (emptyStage_growth_of_zero F hZero)
      hStageFree
  have hZeroNat : Fnat 0 ≤ 0 := by
    simp [Fnat, cardinalGrowth, hZero]
  have hOneNat : Fnat 1 ≤ 2 := by
    simpa [Fnat, cardinalGrowth] using hSingleton
  have hSize : 1 ≤ K 0 := by
    apply cardinalGrowth_inverse F hZero hMono hUnbounded 0 1
    simpa [Fnat, cardinalGrowth] using hSingleton
  intro n
  have hClosed :
      (stage Fnat K n).graph.toPredimension.IsDClosed ∅ Finset.univ :=
    hEmptyClass (stage Fnat K n).carrier
      (stage Fnat K n).graph (hStageGrowth n)
  exact singletonStageRequest_exists
    (stage Fnat K n).graph Fnat K
    hClosed hZeroNat hOneNat hSize


/-- The real-growth class assumptions supply, at *every literal birth
level*, an allowed request with empty named support. This is the
exact extra datum needed to recover level coordinates from
complete-support domains. It strengthens the earlier `Nonempty`
conclusion without an additional class or size assumption. -/
theorem singletonEmptySupportRequest_every_realStage
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2) :
    ∀ n : ℕ,
      ∃ r : StageRequest
        (stage (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) n).graph
        (GrowthAllowedLocal (cardinalGrowth F))
        (fun P => (cardinalGrowthBound F hMono hUnbounded) P.card),
        r.support = ∅ := by
  classical
  let Fnat : ℕ → ℝ := cardinalGrowth F
  let K : ℕ → ℕ := cardinalGrowthBound F hMono hUnbounded
  have hStageFree : ∀ n,
      (stage Fnat K (n + 1)).graph.GrowthClosedUnderDClosedFreeJoins Fnat := by
    intro n
    exact hFree (stage Fnat K (n + 1)).carrier
      (stage Fnat K (n + 1)).graph
  have hStageGrowth : ∀ n,
      (stage Fnat K n).graph.IsGrowthSparse Fnat
        (Finset.univ : Finset (stage Fnat K n).carrier) :=
    all_stages_growth Fnat K (emptyStage_growth_of_zero F hZero)
      hStageFree
  have hZeroNat : Fnat 0 ≤ 0 := by
    simp [Fnat, cardinalGrowth, hZero]
  have hOneNat : Fnat 1 ≤ 2 := by
    simpa [Fnat, cardinalGrowth] using hSingleton
  have hSize : 1 ≤ K 0 := by
    apply cardinalGrowth_inverse F hZero hMono hUnbounded 0 1
    simpa [Fnat, cardinalGrowth] using hSingleton
  intro n
  have hClosed :
      (stage Fnat K n).graph.toPredimension.IsDClosed ∅ Finset.univ :=
    hEmptyClass (stage Fnat K n).carrier
      (stage Fnat K n).graph (hStageGrowth n)
  exact singletonStageRequest_exists_empty_support
    (stage Fnat K n).graph Fnat K
    hClosed hZeroNat hOneNat hSize

/-- The actual canonical C_F birth graph is induced-isomorphic to
every countable comparison graph with the full strict d-closed
genericity properties, under exactly the paper's finite class-level
assumptions and the real-growth hypotheses.

The condition F(1)≤2 is the numerical form of one-vertex
membership; no additional per-stage request hypothesis remains. -/
theorem realBirth_unique_of_growthClassAssumptions
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2)
    (N : GraphOn ℕ)
    (hGrowthN : CFDClosedBackAndForth.HasGrowthInequality (cardinalGrowth F) N)
    (hCoverN : CFDClosedBackAndForth.HasFiniteDClosedCovers N)
    (hResponsesN :
      CFDClosedBackAndForth.HasFiniteDClosedIntervalResponses
        (cardinalGrowth F) N)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ φ : RealBirthVertex F hMono hUnbounded ≃ ℕ,
      ∀ x y : RealBirthVertex F hMono hUnbounded,
        (realCountableGraph F hMono hUnbounded).adj x y ↔
          N.adj (φ x) (φ y) := by
  exact realCountableGraph_unique_of_requests
    F hZero hMono hUnbounded hFree
    (singletonRequest_every_realStage F hZero hMono hUnbounded
      hFree hEmptyClass hSingleton)
    N hGrowthN hCoverN hResponsesN hEmptyN

end CFCoherentTower
end BigHrushovski
