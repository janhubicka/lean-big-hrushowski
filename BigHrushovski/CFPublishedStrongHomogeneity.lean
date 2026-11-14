import BigHrushovski.CFStrictGenericCharacterization
import BigHrushovski.CFPublishedOwnFraissePresentation

/-!
# Strong homogeneity from strictly d-closed finite responses

The existing strict d-closed joint-step theorem and alternating
back-and-forth recursion retain every value of the initial finite
partial isomorphism. Unlike the uniqueness theorem started at the
empty map, this yields strong homogeneity.

This module first makes that consequence explicit for any graph on
the natural-number carrier with finite strict d-closed covers and
prescribed induced finite responses. It then applies it to an
arbitrary genuine natural-number labelling of the *actual* published
C_F birth graph. No weak-strong relaxation, graph homomorphism, or
pre-existing isomorphism with an external Fraisse limit is used.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

/-- Every finite induced partial isomorphism between globally
strictly d-closed subgraphs of a countable strict generic extends to
a total induced automorphism. No global empty-base assumption is
needed here: the recursion starts with the supplied partial
isomorphism, not with the empty map. -/
theorem strictHomogeneous_of_finiteDClosedResponses
    (F : ℕ → ℝ) (M : GraphOn ℕ)
    (hGrowth : HasGrowthInequality F M)
    (hCovers : HasFiniteDClosedCovers M)
    (hResponses : HasFiniteDClosedIntervalResponses F M)
    (p : PartialIso M M) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ, M.adj x y ↔ M.adj (e x) (e y)) ∧
      (∀ x : {x : ℕ // x ∈ p.source},
        e x.val = (p.equiv x).val) := by
  let hJoint : PartialIso.HasJointSteps M M :=
    PartialIso.hasJointSteps_of_finiteDClosedResponses
      F M M hGrowth hGrowth hCovers hCovers
      hResponses hResponses
  exact ⟨PartialIso.equivOfJointSteps p hJoint,
    PartialIso.equivOfJointSteps_induced p hJoint,
    PartialIso.equivOfJointSteps_initial p hJoint⟩

end CFDClosedBackAndForth

namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- For every actual enumerating equivalence of the published C_F
birth carrier with ℕ, the relabelled birth graph is strongly
homogeneous for *strictly d-closed finite induced* partial
isomorphisms: the resulting automorphism extends the prescribed
partial map pointwise.

The enumeration is an explicit hypothesis here. Under the paper's
empty-base and singleton assumptions, its existence has already
been proved by `publishedBirth_standardStrongFraisseLimitPresentation`.
No extra linear order on the finite partial map is used. -/
theorem publishedBirth_relabelled_strongHomogeneous
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (ι : ℕ ≃ PublishedBirthVertex F hMono hUnbounded)
    (p : PartialIso
      ((publishedCountableGraph F hMono hUnbounded).pullback ι)
      ((publishedCountableGraph F hMono hUnbounded).pullback ι)) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        (publishedCountableGraph F hMono hUnbounded).adj (ι x) (ι y) ↔
          (publishedCountableGraph F hMono hUnbounded).adj
            (ι (e x)) (ι (e y))) ∧
      (∀ x : {x : ℕ // x ∈ p.source},
        e x.val = (p.equiv x).val) := by
  let R := extendPublishedGrowth F
  have hZeroR : R 0 = 0 :=
    extendPublishedGrowth_zero F hZero
  have hMonoR : Monotone R :=
    extendPublishedGrowth_monotone F hMono
  have hUnboundedR : ∀ t : ℝ, ∃ x : ℝ, t < R x :=
    extendPublishedGrowth_unbounded F hUnbounded
  have hFreeR : HasFiniteClassDClosedFreeJoins (cardinalGrowth R) := by
    simpa only [publishedCardinalGrowth_eq F] using hFree
  have hNat : HasCountableStrictGenericity (cardinalGrowth R)
      (realCountableGraphNat R hMonoR hUnboundedR ι) :=
    realCountableGraphNat_hasStrictGenericity
      R hZeroR hMonoR hUnboundedR hFreeR ι
  exact strictHomogeneous_of_finiteDClosedResponses
    (cardinalGrowth R)
    (realCountableGraphNat R hMonoR hUnboundedR ι)
    hNat.growth hNat.finite_closed_covers hNat.finite_extensions p


/-- The automorphism constructed on a natural-number presentation
conjugates to a genuine automorphism of the original birth-labelled
carrier. It agrees with the prescribed finite partial map after
transport by the supplied enumeration. No graph reduction or
additional isomorphism with M_F is involved. -/
theorem publishedBirth_strongHomogeneous_onCarrier
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (ι : ℕ ≃ PublishedBirthVertex F hMono hUnbounded)
    (p : PartialIso
      ((publishedCountableGraph F hMono hUnbounded).pullback ι)
      ((publishedCountableGraph F hMono hUnbounded).pullback ι)) :
    ∃ β : PublishedBirthVertex F hMono hUnbounded ≃
        PublishedBirthVertex F hMono hUnbounded,
      (∀ x y : PublishedBirthVertex F hMono hUnbounded,
        (publishedCountableGraph F hMono hUnbounded).adj x y ↔
          (publishedCountableGraph F hMono hUnbounded).adj
            (β x) (β y)) ∧
      (∀ x : {x : ℕ // x ∈ p.source},
        β (ι x.val) = ι (p.equiv x).val) := by
  obtain ⟨e, hAdj, hInitial⟩ :=
    publishedBirth_relabelled_strongHomogeneous
      F hZero hMono hUnbounded hFree ι p
  let β : PublishedBirthVertex F hMono hUnbounded ≃
      PublishedBirthVertex F hMono hUnbounded :=
    ι.symm.trans (e.trans ι)
  refine ⟨β, ?_, ?_⟩
  · intro x y
    simpa only [β, Equiv.trans_apply, Equiv.apply_symm_apply]
      using hAdj (ι.symm x) (ι.symm y)
  · intro x
    calc
      β (ι x.val) = ι (e x.val) := by
        simp only [β, Equiv.trans_apply, Equiv.symm_apply_apply]
      _ = ι (p.equiv x).val := congrArg ι (hInitial x)

end CFCoherentTower
end BigHrushovski
