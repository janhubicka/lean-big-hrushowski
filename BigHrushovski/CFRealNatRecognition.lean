import BigHrushovski.CFCountableRelabelling
import BigHrushovski.CFRealGenericCertificate
import BigHrushovski.CFRealFiniteSubtypeResponse
import BigHrushovski.CFDClosedJointSteps

/-!
# Strict C_F genericity of the birth graph on a natural-number carrier

The canonical C_F graph is constructed on the countable type of
birth-labelled vertices. Given a *genuine equivalence* between ℕ
and that carrier, the induced pullback graph on ℕ satisfies all
four hypotheses of the already verified strict d-closed
back-and-forth uniqueness theorem: growth membership, finite
global strictly d-closed covers, complete finite responses with
a literally prescribed base, and global d-closedness of ∅.

This module does not infer a carrier equivalence from countability
alone. The paper's singleton/empty-base hypotheses must first
establish that the birth carrier is infinite. Nor does this
module postulate a special Fraisse limit M_F: an arbitrary
countable comparison graph N is identified only when N satisfies
the same exact finite strong-limit recognition conditions.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- A natural-number presentation of the actual canonical birth
graph, conditional on an equivalence of vertex sets. -/
noncomputable def realCountableGraphNat
    (F : ℝ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (ι : ℕ ≃ RealBirthVertex F hMono hUnbounded) :
    GraphOn ℕ :=
  (realCountableGraph F hMono hUnbounded).pullback ι

/-- The exact arbitrary finite strict d-closed response property
transports from the birth-labelled graph to its ℕ relabelling.
The given old values, complete induced graph and strictly
d-closed target image are preserved. -/
theorem realCountableGraphNat_finiteResponses
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (ι : ℕ ≃ RealBirthVertex F hMono hUnbounded) :
    HasFiniteDClosedIntervalResponses (cardinalGrowth F)
      (realCountableGraphNat F hMono hUnbounded ι) := by
  classical
  let H : GraphOn (RealBirthVertex F hMono hUnbounded) :=
    realCountableGraph F hMono hUnbounded
  intro M a b hGrowth hab f hfInj hfAdj hfClosed
  let fBirth : {x : ℕ // x ∈ a} →
      RealBirthVertex F hMono hUnbounded := fun x => ι (f x)
  have hfBirthInj : Function.Injective fBirth :=
    ι.injective.comp hfInj
  have hfBirthAdj : ∀ x y : {x : ℕ // x ∈ a},
      M.adj x.val y.val ↔ H.adj (fBirth x) (fBirth y) := by
    intro x y
    exact hfAdj x y
  have hOldImage :
      ((Finset.univ : Finset {x : ℕ // x ∈ a}).image fBirth) =
      (((Finset.univ : Finset {x : ℕ // x ∈ a}).image f).image ι) := by
    rw [Finset.image_image]
    rfl
  have hfBirthClosed :
      H.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {x : ℕ // x ∈ a}).image fBirth) := by
    rw [hOldImage]
    exact (H.globallyDClosed_pullback_iff ι
      ((Finset.univ : Finset {x : ℕ // x ∈ a}).image f)).mp hfClosed
  obtain ⟨gBirth, hgBirthInj, hgBirthOld, hgBirthAdj, hgBirthClosed⟩ :=
    finiteRealDClosedNatInterval_globalResponse
      F hZero hMono hUnbounded M a b hab hGrowth
      fBirth hfBirthInj hfBirthAdj hfBirthClosed
  let g : {x : ℕ // x ∈ b} → ℕ :=
    fun x => ι.symm (gBirth x)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · exact ι.symm.injective.comp hgBirthInj
  · intro x
    change ι.symm (gBirth ⟨x.val, hab.1 x.property⟩) = f x
    rw [hgBirthOld x]
    exact ι.symm_apply_apply (f x)
  · intro x y
    change M.adj x.val y.val ↔
      H.adj (ι (ι.symm (gBirth x))) (ι (ι.symm (gBirth y)))
    simpa only [ι.apply_symm_apply] using hgBirthAdj x y
  · apply (H.globallyDClosed_pullback_iff ι
        ((Finset.univ : Finset {x : ℕ // x ∈ b}).image g)).2
    have hImage :
        (((Finset.univ : Finset {x : ℕ // x ∈ b}).image g).image ι) =
        ((Finset.univ : Finset {x : ℕ // x ∈ b}).image gBirth) := by
      simp [g, Finset.image_image, Function.comp_def]
    rw [hImage]
    exact hgBirthClosed

/-- The actual birth graph satisfies all four hypotheses of the
countable strict d-closed uniqueness theorem after any genuine
relabelling by ℕ. Only the standing class-level d-closed free
amalgamation condition is added to the analytic growth hypotheses. -/
theorem realCountableGraphNat_genericData
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (ι : ℕ ≃ RealBirthVertex F hMono hUnbounded) :
    HasGrowthInequality (cardinalGrowth F)
        (realCountableGraphNat F hMono hUnbounded ι) ∧
      HasFiniteDClosedCovers
        (realCountableGraphNat F hMono hUnbounded ι) ∧
      HasFiniteDClosedIntervalResponses (cardinalGrowth F)
        (realCountableGraphNat F hMono hUnbounded ι) ∧
      (realCountableGraphNat F hMono hUnbounded ι).toPredimension.IsGloballyDClosed ∅ := by
  let H : GraphOn (RealBirthVertex F hMono hUnbounded) :=
    realCountableGraph F hMono hUnbounded
  have cert :=
    realCountableGraph_genericCertificate_of_classFreeJoins
      F hZero hMono hUnbounded hFree
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact H.finiteGrowth_pullback ι (cardinalGrowth F) cert.growth
  · apply H.finiteDClosedCover_pullback ι
    intro s
    obtain ⟨n, hn, hc⟩ := cert.closed_cover s
    exact ⟨stageImage (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) n, hn, hc⟩
  · exact realCountableGraphNat_finiteResponses
      F hZero hMono hUnbounded ι
  · apply (H.globallyDClosed_pullback_iff ι ∅).2
    simpa using cert.empty_closed

/-- Countable C_F generic recognition, once a genuine birth-carrier
equivalence has been given. This is the final conditional
back-and-forth identification with any countable comparison graph
satisfying the *same* growth, finite strict closed-cover and
prescribed extension conditions. It does not assume an existing
graph isomorphism or the desired conclusion. -/
theorem realCountableGraphNat_unique_against
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (ι : ℕ ≃ RealBirthVertex F hMono hUnbounded)
    (N : GraphOn ℕ)
    (hGrowthN : HasGrowthInequality (cardinalGrowth F) N)
    (hCoverN : HasFiniteDClosedCovers N)
    (hResponsesN : HasFiniteDClosedIntervalResponses (cardinalGrowth F) N)
    (hEmptyN : N.toPredimension.IsGloballyDClosed ∅) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      (realCountableGraphNat F hMono hUnbounded ι).adj x y ↔
        N.adj (e x) (e y) := by
  obtain ⟨hGrowth, hCover, hResponses, hEmpty⟩ :=
    realCountableGraphNat_genericData F hZero hMono
      hUnbounded hFree ι
  exact exists_induced_equiv_of_finiteDClosedResponses
    (cardinalGrowth F)
    (realCountableGraphNat F hMono hUnbounded ι) N
    hGrowth hGrowthN hCover hCoverN
    hResponses hResponsesN hEmpty hEmptyN

end CFCoherentTower
end BigHrushovski
