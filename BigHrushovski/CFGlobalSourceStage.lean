import BigHrushovski.CFCountableDClosedChain
import BigHrushovski.CFCountableGrowth

/-!
# Put a globally d-closed finite source in an actual finite C_F stage

Every finite set of birth-labelled vertices is covered by a
canonical stage image. For a globally strictly d-closed finite
source S in the countable graph, pull S back along that induced
stage embedding. Its literal preimage A is d-closed in the
finite stage, because global strict d-closedness restricts to
the stage and induced embeddings preserve exact predimension.

This is the starting point needed for the generic extension
property: one may answer an arbitrary given globally
d-closed copy at an actual stage without changing its
vertex names or first replacing it by an isomorphic copy.

It does not construct any requested extension or claim
completeness of the local catalogue.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Any finite globally strictly d-closed subset of the
birth-labelled countable graph is exactly the induced image
of a strictly d-closed subset of some actual finite stage. -/
theorem globalFiniteSource_in_dClosedStage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hGlobal : (countableGraph F K).toPredimension.IsGloballyDClosed s) :
    ∃ n : ℕ, ∃ a : Finset (stage F K n).carrier,
      s = a.image (toVertex F K n) ∧
      (stage F K n).graph.toPredimension.IsDClosed
        a Finset.univ := by
  classical
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let a : Finset (stage F K n).carrier :=
    (Finset.univ : Finset (stage F K n).carrier).filter
      (fun v => toVertex F K n v ∈ s)
  have hImage : a.image (toVertex F K n) = s :=
    GraphOn.finite_image_preimage_within
      (toVertex F K n)
      (Finset.univ : Finset (stage F K n).carrier)
      s hCover
  have hWithin : (countableGraph F K).toPredimension.IsDClosed
      s (stageImage F K n) :=
    (countableGraph F K).toPredimension.IsGloballyDClosed.restrict
      hGlobal hCover
  have hStage : (stage F K n).graph.toPredimension.IsDClosed
      a Finset.univ := by
    apply (((stage F K n).graph).dClosed_image_iff
      (countableGraph F K) (toVertex F K n)
      (toVertex_injective F K n)
      (fun u v => (countableGraph_stage_induced F K n u v).symm)
      a Finset.univ (Finset.subset_univ _)).mp
    simpa only [hImage, stageImage] using hWithin
  exact ⟨n, a, hImage.symm, hStage⟩

end CFCoherentTower
end BigHrushovski
