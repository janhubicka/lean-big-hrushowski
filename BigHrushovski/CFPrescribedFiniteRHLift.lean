import BigHrushovski.CFPrescribedFiniteOrderedLift
import BigHrushovski.CFCanonicalOrderEmbedding

/-!
# Finite prescribed C_F lifts in the exact (R,H) functional language

The finite C_F lift already preserves the complete auxiliary b-values
and is induced, injective, birth-level-preorder preserving, and
increasing for the manuscript's actual canonical birth order.
The previously verified closed-source equivalence between b and
(R,H) embeddings can therefore be applied to the actual finite
source. This supplies all R(v), every defined H(S), and reflection
of the partial H-domain, without building an ambient self-embedding.

The extension of the finite map by the identity outside its source
is ONLY a way of evaluating the ambient finset-valued operations.
It is never asserted to be a graph embedding outside the source.

No uniqueness of arbitrary finite functional embeddings is claimed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A finite b-closed set is also closed in the equivalent
subset-based presentation, without requiring infinitude or
closure under any larger generated set. -/
theorem finiteBirthBlockClosed_as_closedSet
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) :
    IsBirthBlockClosedSet F K {v | v ∈ s} := by
  intro n r i hv
  exact hs n r i hv

/-- For the actual finite prescribed lift, extending the map by
identity off its finite source preserves the COMPLETE ambient
b-value at every source vertex. No property is assumed or used
on the complement of the source. -/
theorem finiteSourcePrescribedLift_extendedBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    let X : Set (Vertex F K) := {v | v ∈ s}
    let e : {v : Vertex F K // v ∈ X} → Vertex F K :=
      finiteSourcePrescribedLift F K s hs level hStrict n hCover
    let f := extendClosedSourceMap F K X e
    ∀ v ∈ X,
      (birthBValue F K v).image f = birthBValue F K (f v) := by
  let X : Set (Vertex F K) := {v | v ∈ s}
  let e : {v : Vertex F K // v ∈ X} → Vertex F K :=
    finiteSourcePrescribedLift F K s hs level hStrict n hCover
  let f := extendClosedSourceMap F K X e
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  change ∀ v ∈ X,
    (birthBValue F K v).image f = birthBValue F K (f v)
  intro v hv
  let a : SupportCarrier (Vertex F K) s := ⟨v, hv⟩
  have hRestricted :
      (finiteSourceBirthBValue F K s a).image e =
        birthBValue F K (e a) :=
    finiteSourceLiftOfCut_birthBValues F K s hs n
      (assignedTargetStage F K s level n) hCover M.map a
  have hAmbient :
      (finiteSourceBirthBValue F K s a).image Subtype.val =
        birthBValue F K v :=
    finiteSourceBirthBValue_image F K s hs a
  calc
    (birthBValue F K v).image f =
        ((finiteSourceBirthBValue F K s a).image Subtype.val).image f := by
          rw [hAmbient]
    _ = (finiteSourceBirthBValue F K s a).image e := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro u hu
          exact extendClosedSourceMap_apply F K X e u.val u.property
    _ = birthBValue F K (e a) := hRestricted
    _ = birthBValue F K (f v) := by
          rw [extendClosedSourceMap_apply F K X e v hv]

/-- The exact prescribed finite lift preserves full R(v)-values,
all defined H-values, and the domain of the partial H-operation.
The same concrete map also satisfies the complete ordered
b-functional existence theorem; no separate witness is chosen.

There are NO hypotheses about the map outside the finite source.
In particular it is not assumed to extend to an embedding of the
whole countable graph, or to a strictly increasing map of all birth
levels. -/
theorem finiteSourcePrescribedLift_RHValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    let X : Set (Vertex F K) := {v | v ∈ s}
    let e : {v : Vertex F K // v ∈ X} → Vertex F K :=
      finiteSourcePrescribedLift F K s hs level hStrict n hCover
    let f := extendClosedSourceMap F K X e
    (∀ v ∈ X,
      (birthReachableRoots F K v).image f =
        birthReachableRoots F K (f v)) ∧
    (∀ t : Finset (Vertex F K),
      (∀ v ∈ t, v ∈ X) →
      (∀ r ∈ t, IsBirthRoot F K r) →
      (birthDClosedHull F K t).image f =
        birthDClosedHull F K (t.image f)) ∧
    (∀ t : Finset (Vertex F K),
      (∀ v ∈ t, v ∈ X) →
      ((∀ r ∈ t, IsBirthRoot F K r) ↔
        (∀ r ∈ t.image f, IsBirthRoot F K r))) := by
  let X : Set (Vertex F K) := {v | v ∈ s}
  let e : {v : Vertex F K // v ∈ X} → Vertex F K :=
    finiteSourcePrescribedLift F K s hs level hStrict n hCover
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  have hX : IsBirthBlockClosedSet F K X :=
    finiteBirthBlockClosed_as_closedSet F K s hs
  have heInj : Function.Injective e :=
    finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover M.map
  have heAdj : ∀ u v : {v : Vertex F K // v ∈ X},
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (e u) (e v) := by
    intro u v
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover M.map u v
  have heLevel : ∀ u v : {v : Vertex F K // v ∈ X},
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (e u) (e v) := by
    intro u v
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover u v
  have heOrder : ∀ u v : {v : Vertex F K // v ∈ X},
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (e u) (e v) := by
    intro u v
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrict n hCover u v
  have hEquiv :=
    literalClosedSource_bValues_iff_RHValues_of_canonicalOrder
      F K X hX e heInj heAdj heLevel heOrder
  exact hEquiv.mp
    (finiteSourcePrescribedLift_extendedBValues
      F K s hs level hStrict n hCover)

end CFCoherentTower
end BigHrushovski
