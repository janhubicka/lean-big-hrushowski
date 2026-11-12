import BigHrushovski.CFStandardFraisseExtension
import BigHrushovski.CFPublishedFiniteGenericity
import BigHrushovski.CFRealGenericCertificate
import BigHrushovski.CFSingletonStageCoverage
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic

/-!
# The actual published birth graph is a standard strong Fraisse limit

The existing identification theorem compares the canonical birth graph
with an independently presented countable strong Fraisse limit. This file
also establishes the defining strong Fraisse-limit properties directly on
the actual birth-labelled carrier.

The only nontrivial interface left by the linearly ordered finite response
theorem is arbitrary finite source types. Choose an auxiliary linear order
on each finite type using an equivalence with a finite ordinal, apply the
already proved induced and globally strictly closed response, and forget
that auxiliary order. The resulting map has the original source labels
and preserves the original prescribed embedding pointwise.

No comparison model, prior graph isomorphism, or additional properties
of the growth function are hypotheses of the final certificate.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics CFDClosedBackAndForth

/-- A classical equality decision procedure for the countable birth
carrier. This is a computational convenience needed by the finite
image API, not a finiteness or additional graph hypothesis. -/
noncomputable instance publishedBirthVertex_decidableEq
    (F : PublishedGrowth)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val) :
    DecidableEq (PublishedBirthVertex F hMono hUnbounded) :=
  Classical.decEq _

/-- The actual published birth graph realizes every finite strong
extension over any prescribed globally strictly d-closed induced
embedding, even if the finite source carrier has no given linear
order. The temporary order is used only to apply the already
certified finite response theorem; it is not retained in the
conclusion. -/
theorem publishedBirth_hasStandardFiniteDClosedExtensions
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val) :
    HasStandardFiniteDClosedExtensions (publishedCardinalGrowth F)
      (publishedCountableGraph F hMono hUnbounded) := by
  classical
  intro W _ _ B a hGrowth hClosed f hfInj hfAdj hfStrong
  let eFin : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  letI : LinearOrder W :=
    LinearOrder.lift' (fun w : W => eFin w) eFin.injective
  obtain ⟨g0, hg0Inj, hg0Old, hg0Adj, hg0Closed⟩ :=
    finitePublishedDClosedInterval_globalResponse
      B F hZero hMono hUnbounded hGrowth
      a Finset.univ hClosed f hfInj hfAdj hfStrong
  let g : W → PublishedBirthVertex F hMono hUnbounded :=
    fun w => g0 ⟨w, Finset.mem_univ _⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hSub :
        (⟨x, Finset.mem_univ _⟩ :
          {w : W // w ∈ (Finset.univ : Finset W)}) =
        ⟨y, Finset.mem_univ _⟩ := hg0Inj hxy
    exact congrArg Subtype.val hSub
  · intro x
    simpa [g] using hg0Old x
  · intro x y
    exact hg0Adj ⟨x, Finset.mem_univ _⟩ ⟨y, Finset.mem_univ _⟩
  · convert hg0Closed using 1
    ext v
    constructor
    · intro hv
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨⟨w, Finset.mem_univ _⟩, Finset.mem_univ _, hw⟩
    · intro hv
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨w.val, Finset.mem_univ _, hw⟩

/-- The canonical birth graph, with its *actual* vertex names, has
the ordinary strong Fraisse-limit presentation of the manuscript:
a countably infinite carrier, full finite C_F age, a covering finite
strictly d-closed chain, and the arbitrary-finite prescribed-base
strong extension property.

Existence is established directly from the construction. In particular
no independent comparison graph M_F, no assumed isomorphism and no
extra per-level request hypothesis are used. -/
noncomputable def publishedBirth_standardStrongFraisseLimitPresentation
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hFree : HasFiniteClassDClosedFreeJoins
      (publishedCardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass
      (publishedCardinalGrowth F))
    (hSingleton : (F ⟨(1 : ℝ), by norm_num⟩).val ≤ 2) :
    StandardStrongFraisseLimitPresentation
      (publishedCardinalGrowth F)
      (publishedCountableGraph F hMono hUnbounded) := by
  classical
  let R := extendPublishedGrowth F
  have hZeroR : R 0 = 0 := extendPublishedGrowth_zero F hZero
  have hMonoR : Monotone R := extendPublishedGrowth_monotone F hMono
  have hUnboundedR : ∀ t : ℝ, ∃ x : ℝ, t < R x :=
    extendPublishedGrowth_unbounded F hUnbounded
  have hFreeR : HasFiniteClassDClosedFreeJoins (cardinalGrowth R) := by
    simpa only [publishedCardinalGrowth_eq F] using hFree
  have hEmptyR : EmptyDClosedInGrowthClass (cardinalGrowth R) := by
    simpa only [publishedCardinalGrowth_eq F] using hEmptyClass
  have hOneR : R 1 ≤ 2 := by
    simpa [R, extendPublishedGrowth] using hSingleton
  have hRequests := singletonRequest_every_realStage
    R hZeroR hMonoR hUnboundedR hFreeR hEmptyR hOneR
  let ι : ℕ ≃ PublishedBirthVertex F hMono hUnbounded :=
    natEquivBirth_of_requests
      (cardinalGrowth R) (cardinalGrowthBound R hMonoR hUnboundedR)
      hRequests
  have hCertificate : RealGrowthGenericCertificate
      R hMonoR hUnboundedR :=
    realCountableGraph_genericCertificate_of_classFreeJoins
      R hZeroR hMonoR hUnboundedR hFreeR
  refine {
    enumerate := ι
    age := ?_
    chain := birthDClosedChain
      (cardinalGrowth R) (cardinalGrowthBound R hMonoR hUnboundedR)
    standard_extensions := publishedBirth_hasStandardFiniteDClosedExtensions
      F hZero hMono hUnbounded
  }
  intro s
  change publishedCardinalGrowth F s.card ≤
    ((realCountableGraph R hMonoR hUnboundedR).predim s : ℝ)
  calc
    publishedCardinalGrowth F s.card =
        cardinalGrowth R s.card :=
      congrFun (publishedCardinalGrowth_eq F) s.card
    _ ≤ _ := hCertificate.growth s

/-- Every finite graph in the published growth class has an induced,
globally strictly d-closed copy in the actual birth graph. This proves
the *other* inclusion in the finite-age assertion: the growth
certificate alone only says that finite induced birth subgraphs
belong to C_F.

The copy is obtained by applying the ordinary finite extension theorem
over the literally empty strong base. No arbitrary enumeration of the
finite source and no external Fraisse-limit isomorphism is used. -/
theorem publishedBirth_finiteStrongUniversality
    (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ,
      ∃ x : NonnegativeReal, t < (F x).val)
    (hEmptyClass : EmptyDClosedInGrowthClass
      (publishedCardinalGrowth F))
    (W : Type) [Fintype W] [DecidableEq W]
    (B : GraphOn W)
    (hGrowth : B.IsGrowthSparse (publishedCardinalGrowth F)
      (Finset.univ : Finset W)) :
    ∃ g : W → PublishedBirthVertex F hMono hUnbounded,
      Function.Injective g ∧
      (∀ x y : W,
        B.adj x y ↔
          (publishedCountableGraph F hMono hUnbounded).adj (g x) (g y)) ∧
      (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset W).image g) := by
  classical
  have hBaseClosed :
      B.toPredimension.IsDClosed (∅ : Finset W) Finset.univ :=
    hEmptyClass W B hGrowth
  have emptyElim (x : {w : W // w ∈ (∅ : Finset W)}) : False :=
    Finset.notMem_empty x.val x.property
  let e : {w : W // w ∈ (∅ : Finset W)} →
      PublishedBirthVertex F hMono hUnbounded :=
    fun x => False.elim (emptyElim x)
  have heInj : Function.Injective e := by
    intro x y _
    exact False.elim (emptyElim x)
  have heAdj : ∀ x y : {w : W // w ∈ (∅ : Finset W)},
      B.adj x.val y.val ↔
        (publishedCountableGraph F hMono hUnbounded).adj (e x) (e y) := by
    intro x y
    exact False.elim (emptyElim x)
  have hEmptyImage :
      ((Finset.univ : Finset {w : W // w ∈ (∅ : Finset W)}).image e) =
        (∅ : Finset (PublishedBirthVertex F hMono hUnbounded)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, _, _⟩ := Finset.mem_image.mp hv
      exact False.elim (emptyElim x)
    · simp
  have hTargetEmpty :
      (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        (∅ : Finset (PublishedBirthVertex F hMono hUnbounded)) :=
    realCountableGraph_empty_globalDClosed
      (extendPublishedGrowth F)
      (extendPublishedGrowth_monotone F hMono)
      (extendPublishedGrowth_unbounded F hUnbounded)
  have heStrong :
      (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {w : W // w ∈ (∅ : Finset W)}).image e) := by
    exact hEmptyImage.symm ▸ hTargetEmpty
  obtain ⟨g, hgInj, _, hgAdj, hgStrong⟩ :=
    publishedBirth_hasStandardFiniteDClosedExtensions
      F hZero hMono hUnbounded W B ∅ hGrowth hBaseClosed
      e heInj heAdj heStrong
  exact ⟨g, hgInj, hgAdj, hgStrong⟩

end CFCoherentTower
end BigHrushovski
