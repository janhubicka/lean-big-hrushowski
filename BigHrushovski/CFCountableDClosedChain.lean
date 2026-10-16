import BigHrushovski.CFCountableGrowth
import BigHrushovski.CFDClosedChain

/-!
# Globally d-closed stages of the countable C_F birth graph

The finite tagged stage U_n is strictly d-closed in U_(n+1).
We have proved that the birth-labelled countable graph contains
each finite stage as an induced graph. Transport the one-step
strict d-closed relation into this common ambient countable
graph using the canonical birth maps.

The stage images are finite and cover the countable carrier.
They therefore form a genuine Predimension.DClosedChain.
The existing reusable stage_global theorem immediately shows
that every finite stage is *globally* strictly d-closed in
the countable graph.

This module deliberately does not assert the generic finite
extension property: completeness of all local requests
still requires the published size bound and the actual
minimal-step response argument.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The entire old stage image computed inside its successor
is exactly its original birth-labelled stage image. -/
theorem stageImage_succ_old
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    stageImage F K n =
      (((Finset.univ : Finset (stage F K n).carrier).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n + 1)).carrier)).image
        (toVertex F K (n + 1))) := by
  classical
  simp only [stageImage, Finset.image_image, toVertex_old]

/-- The finite strict d-closed successor relation transfers
through an exact induced birth-labelled stage map. -/
theorem stageImage_dClosed_succ
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    (countableGraph F K).toPredimension.IsDClosed
      (stageImage F K n) (stageImage F K (n + 1)) := by
  classical
  have hStage := stage_succ_dClosed F K n
  have hInduced : ∀ a b : (stage F K (n + 1)).carrier,
      (stage F K (n + 1)).graph.adj a b ↔
        (countableGraph F K).adj
          (toVertex F K (n + 1) a)
          (toVertex F K (n + 1) b) := by
    intro a b
    exact (countableGraph_stage_induced F K (n + 1) a b).symm
  have hImage :=
    (((stage F K (n + 1)).graph).dClosed_image_iff
      (countableGraph F K) (toVertex F K (n + 1))
      (toVertex_injective F K (n + 1))
      hInduced
      ((Finset.univ : Finset (stage F K n).carrier).image
        (Sum.inl : (stage F K n).carrier →
          (stage F K (n + 1)).carrier))
      Finset.univ (Finset.subset_univ _)).mpr hStage
  simpa only [stageImage, Finset.image_image, toVertex_old] using hImage

/-- The actual embedded finite stages form a strict d-closed
covering chain in one fixed, countable ambient graph. -/
noncomputable def birthDClosedChain
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Predimension.DClosedChain (countableGraph F K).toPredimension where
  stage := stageImage F K
  dclosed_step := stageImage_dClosed_succ F K
  covers := by
    intro v
    exact vertex_in_some_stageImage F K v

/-- Every tagged finite C_F stage is globally strictly
d-closed in the countable birth graph, with strictness
tested against *all* finite proper supersets. -/
theorem stageImage_global_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      (stageImage F K n) :=
  (birthDClosedChain F K).stage_global n

end CFCoherentTower
end BigHrushovski
