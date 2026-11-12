import BigHrushovski.CFArbitraryFiniteRHUniqueness
import BigHrushovski.CFPrescribedFiniteRHLift

/-!
# Complete finite unique level lifting for the C_F birth structure

The constructed prescribed finite lift already establishes existence:
for any finite b-closed source and every assignment strictly increasing
on its represented birth levels, it gives one injective induced
embedding preserving the complete b-value, actual canonical order,
birth-level preorder, and exact prescribed birth labels. The same
map preserves the genuine R and partial H operations, including
reflection of H's domain.

The arbitrary finite uniqueness induction proves that no second
embedding with these exact data exists. Combining both arguments
now yields the existence-and-uniqueness statement needed by the
manuscript, first in the auxiliary b-language, then in the actual
(R,H) language. Empty sources and arbitrary gaps in represented
source and target levels are included without separate cases.

This is a finite result. Compatibility of lifts under restrictions
and composition, and the monoid of countable self-embeddings,
are separate subsequent statements.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every strictly increasing assignment of the FINITELY
represented source birth levels has a unique embedding in
the complete auxiliary b-functional birth language, including
the actual canonical order, reflected level preorder, induced
graph and exact complete unary b-values.

No extension of the level assignment to a globally increasing
map on all natural numbers is assumed. -/
theorem finiteSourcePrescribedLift_existsUnique_orderedB
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃! f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image f =
          birthBValue F K (f x)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (f x).1 = level x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (f x) (f y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (f x) (f y)) := by
  obtain ⟨f, hfInj, hfAdj, hfB, hfBirth, hfLevel, hfOrder⟩ :=
    finiteSourcePrescribedLift_exists_ordered
      F K s hs level hStrict
  refine ⟨f, ⟨hfInj, hfAdj, hfB, hfBirth, hfLevel, hfOrder⟩, ?_⟩
  intro g ⟨hgInj, hgAdj, hgB, hgBirth, hgLevel, hgOrder⟩
  exact arbitraryFiniteEmbedding_unique_of_prescribedLevels
    F K s hs level g f hgInj hfInj hgAdj hfAdj hgB hfB
    hgLevel hfLevel hgOrder hfOrder hgBirth hfBirth

/-- Complete finite unique level lifting in the manuscript's
actual (R,H) functional language. The operation H is PARTIAL:
the theorem requires exact transport of all its defined
finite-set values AND reflection of its domain. The same
concrete constructed map simultaneously witnesses all conditions.

This result establishes existence AND uniqueness among ALL
admissible finite R/H embeddings with the prescribed target
birth-level assignment; it does not assume that an arbitrary
embedding is already the canonical lift. -/
theorem finiteSourcePrescribedLift_existsUnique_RH
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃! f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (f x).1 = level x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (f x) (f y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (f x) (f y)) ∧
      (let X : Set (Vertex F K) := {v | v ∈ s}
       let f' := extendClosedSourceMap F K X f
       (∀ v ∈ X,
          (birthReachableRoots F K v).image f' =
            birthReachableRoots F K (f' v)) ∧
       (∀ t : Finset (Vertex F K),
          (∀ v ∈ t, v ∈ X) →
          (∀ r ∈ t, IsBirthRoot F K r) →
          (birthDClosedHull F K t).image f' =
            birthDClosedHull F K (t.image f')) ∧
       (∀ t : Finset (Vertex F K),
          (∀ v ∈ t, v ∈ X) →
          ((∀ r ∈ t, IsBirthRoot F K r) ↔
            (∀ r ∈ t.image f', IsBirthRoot F K r)))) := by
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  let f := finiteSourcePrescribedLift F K s hs level hStrict n hCover
  have hfInj : Function.Injective f :=
    finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover M.map
  have hfAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (f x) (f y) := by
    intro x y
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover M.map x y
  have hfBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (f x).1 = level x.val.1 := by
    intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrict n hCover x
  have hfLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (f x) (f y) := by
    intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover x y
  have hfOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (f x) (f y) := by
    intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrict n hCover x y
  have hfRH :
      let X : Set (Vertex F K) := {v | v ∈ s}
      let f' := extendClosedSourceMap F K X f
      (∀ v ∈ X,
          (birthReachableRoots F K v).image f' =
            birthReachableRoots F K (f' v)) ∧
      (∀ t : Finset (Vertex F K),
          (∀ v ∈ t, v ∈ X) →
          (∀ r ∈ t, IsBirthRoot F K r) →
          (birthDClosedHull F K t).image f' =
            birthDClosedHull F K (t.image f')) ∧
      (∀ t : Finset (Vertex F K),
          (∀ v ∈ t, v ∈ X) →
          ((∀ r ∈ t, IsBirthRoot F K r) ↔
            (∀ r ∈ t.image f', IsBirthRoot F K r))) :=
    finiteSourcePrescribedLift_RHValues
      F K s hs level hStrict n hCover
  refine ⟨f, ⟨hfInj, hfAdj, hfBirth, hfLevel, hfOrder, hfRH⟩, ?_⟩
  intro g ⟨hgInj, hgAdj, hgBirth, hgLevel, hgOrder, hgRH⟩
  exact arbitraryFiniteRHEmbedding_unique_of_prescribedLevels
    F K s hs level g f hgInj hfInj hgAdj hfAdj
    hgLevel hfLevel hgOrder hfOrder hgRH hfRH
    hgBirth hfBirth

end CFCoherentTower
end BigHrushovski
