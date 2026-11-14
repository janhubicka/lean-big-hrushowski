import BigHrushovski.CFFiniteClosedSourceRestriction
import BigHrushovski.CFArbitraryFiniteUniqueness

/-!
# Finite C_F prescribed lifts commute with closed-source restriction

Let s be a finite b-closed substructure of a finite b-closed
substructure t. A level assignment strictly increasing on levels
represented by t also applies to s. The prescribed finite
lift of t restricts to an embedding of s, preserving all complete
birth-b-values, induced graph adjacency/nonadjacency,
the canonical birth order and reflected birth-level preorder.

The arbitrary finite uniqueness theorem therefore identifies
that restriction with the prescribed finite lift of s. This
works independently of the finite stage covers chosen in the
two existence constructions and does not use a global
increasing map of all birth levels.

This proves restriction compatibility in the auxiliary
b-functional language; transport to R/H and composition
compatibility remain separate steps.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The particular finite prescribed lift of a larger b-closed
source restricts to the SAME actual birth-labelled map as the
particular prescribed lift of a smaller closed source.

The two finite source coverings nS and nT can be completely
different. Equality comes from arbitrary-map finite uniqueness,
not from identifying two recursive finite-stage constructions. -/
theorem finiteSourcePrescribedLift_restriction
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (ht : IsBirthBlockClosed F K t)
    (hst : s ⊆ t)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K t level)
    (nS nT : ℕ)
    (hCoverS : s ⊆ stageImage F K nS)
    (hCoverT : t ⊆ stageImage F K nT) :
    let hStrictS :=
      strictOnRepresented_of_subset F K s t hst level hStrict
    (fun x : SupportCarrier (Vertex F K) s =>
       finiteSourcePrescribedLift
         F K t ht level hStrict nT hCoverT
         (finiteClosedSourceInclusion F K s t hst x)) =
      finiteSourcePrescribedLift
        F K s hs level hStrictS nS hCoverS := by
  let hStrictS :=
    strictOnRepresented_of_subset F K s t hst level hStrict
  let i := finiteClosedSourceInclusion F K s t hst
  let MT := finiteLevelCutLiftWithBirth F K t ht level hStrict nT
  let MS := finiteLevelCutLiftWithBirth F K s hs level hStrictS nS
  let Et := finiteSourcePrescribedLift
    F K t ht level hStrict nT hCoverT
  let Es := finiteSourcePrescribedLift
    F K s hs level hStrictS nS hCoverS
  let restr : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => Et (i x)
  have htInj : Function.Injective Et :=
    finiteSourceLiftOfCut_injective F K t nT
      (assignedTargetStage F K t level nT) hCoverT MT.map
  have hsInj : Function.Injective Es :=
    finiteSourceLiftOfCut_injective F K s nS
      (assignedTargetStage F K s level nS) hCoverS MS.map
  have hRestrInj : Function.Injective restr := by
    intro x y hxy
    exact finiteClosedSourceInclusion_injective
      F K s t hst (htInj hxy)
  have hRestrAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (restr x) (restr y) := by
    intro x y
    exact finiteSourceLiftOfCut_induced F K t nT
      (assignedTargetStage F K t level nT) hCoverT MT.map
      (i x) (i y)
  have hEtB : ∀ x : SupportCarrier (Vertex F K) t,
      (finiteSourceBirthBValue F K t x).image Et =
        birthBValue F K (Et x) := by
    intro x
    exact finiteSourceLiftOfCut_birthBValues F K t ht nT
      (assignedTargetStage F K t level nT) hCoverT MT.map x
  have hRestrB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image restr =
        birthBValue F K (restr x) := by
    intro x
    exact finiteSourceBirthBValue_restriction
      F K s t hs ht hst Et hEtB x
  have hRestrBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (restr x).1 = level x.val.1 := by
    intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K t ht level hStrict nT hCoverT (i x)
  have hRestrLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (restr x) (restr y) := by
    intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K t ht level hStrict nT hCoverT (i x) (i y)
  have hRestrOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (restr x) (restr y) := by
    intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K t ht level hStrict nT hCoverT (i x) (i y)
  have hsAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (Es x) (Es y) := by
    intro x y
    exact finiteSourceLiftOfCut_induced F K s nS
      (assignedTargetStage F K s level nS) hCoverS MS.map x y
  have hsB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image Es =
        birthBValue F K (Es x) := by
    intro x
    exact finiteSourceLiftOfCut_birthBValues F K s hs nS
      (assignedTargetStage F K s level nS) hCoverS MS.map x
  have hsBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (Es x).1 = level x.val.1 := by
    intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrictS nS hCoverS x
  have hsLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (Es x) (Es y) := by
    intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrictS nS hCoverS x y
  have hsOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (Es x) (Es y) := by
    intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrictS nS hCoverS x y
  exact arbitraryFiniteEmbedding_unique_of_prescribedLevels
    F K s hs level restr Es
    hRestrInj hsInj hRestrAdj hsAdj hRestrB hsB
    hRestrLevel hsLevel hRestrOrder hsOrder
    hRestrBirth hsBirth

end CFCoherentTower
end BigHrushovski
