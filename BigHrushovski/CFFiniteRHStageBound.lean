import BigHrushovski.CFFiniteRHIntrinsicLevelClassification
import BigHrushovski.CFBirthGeneratedClosure

/-!
# Exact stage bound for finite prescribed R/H level lifts

The finite Ramsey argument requires a precise stage-containment
property in addition to existence and uniqueness: a finite
functional source whose represented birth levels are sent below
N must have its entire lifted image inside the literal U_N.

For the actual birth-labelled carrier, stage membership is
equivalent to the inequality birthLevel < N. We combine this
with the verified exact level action of any finite R/H embedding,
without requiring a total map on old stages or a globally
increasing map on all of omega.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every finite R/H level embedding with target birth levels
strictly below N has its ENTIRE literal image inside U_N.
It is enough to bound the levels represented in its finite
source. No condition on unrepresented levels is assumed.

The result includes the empty source and N = 0: in that case
the hypotheses are satisfied only when no mapped vertex exists. -/
theorem finiteRHLevelEmbedding_image_subset_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (he : FiniteRHLevelEmbedding F K s level e)
    (N : ℕ)
    (hBound : ∀ i ∈ representedLevels F K s, level i < N) :
    ∀ x : SupportCarrier (Vertex F K) s,
      e x ∈ stageImage F K N := by
  obtain ⟨_, _, hBirth, _, _, _⟩ := he
  intro x
  apply (mem_stageImage_iff_birth_lt F K N (e x)).mpr
  rw [hBirth x]
  exact hBound x.val.1
    (Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩)

/-- Every strictly increasing assignment of the represented
source levels to levels below N has a UNIQUE finite embedding
of the actual ordered partial R/H language whose image
lies inside the literal finite birth stage U_N.

The source is a genuine finite R/H-substructure, and the
embedding preserves complete R-values, all defined partial
H-values, reflection of H's domain, induced edges/nonedges,
birth-level preorder and canonical order. No separate
target-stage map is imposed. -/
theorem finiteRHClosed_existsUnique_levelLift_in_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (N : ℕ)
    (hBound : ∀ i ∈ representedLevels F K s, level i < N) :
    ∃! e : SupportCarrier (Vertex F K) s → Vertex F K,
      FiniteRHLevelEmbedding F K s level e ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        e x ∈ stageImage F K N) := by
  obtain ⟨e, he, hUnique⟩ :=
    finiteRHClosed_existsUnique_levelLift
      F K s hsRH level hStrict
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · exact finiteRHLevelEmbedding_image_subset_stage
      F K s level e he N hBound
  · intro g hg
    exact hUnique g hg.1

/-- A finite R/H embedding is stage-bounded precisely when
all of its represented target levels are below the stage.
This can be used to check containment of ANY arbitrary
finite embedding without recognizing it as a chosen lift. -/
theorem finiteRHLevelEmbedding_image_subset_stage_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (he : FiniteRHLevelEmbedding F K s level e)
    (N : ℕ) :
    (∀ x : SupportCarrier (Vertex F K) s,
      e x ∈ stageImage F K N) ↔
      (∀ i ∈ representedLevels F K s, level i < N) := by
  constructor
  · intro hImage i hi
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    let x : SupportCarrier (Vertex F K) s := ⟨v, hv⟩
    have hLevel : (e x).1 = level x.val.1 := he.2.2.1 x
    have hBorn : (e x).1 < N :=
      (mem_stageImage_iff_birth_lt F K N (e x)).mp (hImage x)
    have hTarget : level x.val.1 < N := by
      rw [← hLevel]
      exact hBorn
    simpa only [x, hvi] using hTarget
  · intro hBound
    exact finiteRHLevelEmbedding_image_subset_stage
      F K s level e he N hBound

end CFCoherentTower
end BigHrushovski
