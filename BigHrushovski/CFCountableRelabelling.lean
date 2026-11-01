import BigHrushovski.CFDClosedChain
import BigHrushovski.CFGrowthClass
import BigHrushovski.InducedEmbedding

/-!
# Strict d-closedness and growth inequalities under graph relabelling

A countable birth-labelled graph can be compared with a graph on ℕ
only after choosing a genuine carrier equivalence. The induced graph
under this equivalence must retain all edges and nonedges, all finite
predimensions, global *strict* d-closedness and finite closed covers.

The arguments are valid for any equivalence of vertex types, not just
for the C_F birth carrier, and may also be reused for finite
graph-presentation questions. They do not postulate a carrier
equivalence or assume that a merely countable type is infinite.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Global strict d-closedness is exactly invariant under a
bijective relabelling of the entire graph. An induced injection
whose image is not the whole ambient vertex set would not suffice. -/
theorem globallyDClosed_pullback_iff
    (G : GraphOn V) (e : U ≃ V) (a : Finset U) :
    (G.pullback e).toPredimension.IsGloballyDClosed a ↔
      G.toPredimension.IsGloballyDClosed (a.image e) := by
  classical
  have hAdj : ∀ x y : U,
      (G.pullback e).adj x y ↔ G.adj (e x) (e y) :=
    fun _ _ => Iff.rfl
  have hPredim (s : Finset U) :
      G.predim (s.image e) = (G.pullback e).predim s :=
    (G.pullback e).predim_image G e e.injective hAdj s
  constructor
  · intro hSource b hab hne
    let t : Finset U := b.image e.symm
    have htImage : t.image e = b := by
      simp [t, Finset.image_image, Function.comp_def]
    have hat : a ⊆ t := by
      intro x hx
      apply Finset.mem_image.mpr
      refine ⟨e x, hab ?_, e.symm_apply_apply x⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hne' : t ≠ a := by
      intro hta
      apply hne
      calc
        b = t.image e := htImage.symm
        _ = a.image e := by rw [hta]
    have hStrict := hSource t hat hne'
    change (G.pullback e).predim a < (G.pullback e).predim t at hStrict
    rw [← hPredim a, ← hPredim t] at hStrict
    simpa only [htImage] using hStrict
  · intro hTarget b hab hne
    have hne' : b.image e ≠ a.image e := by
      intro hEq
      exact hne ((Finset.image_injective e.injective) hEq)
    have hStrict :=
      hTarget (b.image e) (Finset.image_mono e hab) hne'
    change G.predim (a.image e) < G.predim (b.image e) at hStrict
    simpa only [hPredim a, hPredim b] using hStrict

/-- Strict finite closed-cover existence is invariant under a genuine
carrier equivalence. The cover is still finite and globally d-closed
against *all* finite supersets of the new ambient graph. -/
theorem finiteDClosedCover_pullback
    (G : GraphOn V) (e : U ≃ V)
    (hCover : ∀ s : Finset V,
      ∃ c : Finset V, s ⊆ c ∧
        G.toPredimension.IsGloballyDClosed c) :
    ∀ s : Finset U,
      ∃ c : Finset U, s ⊆ c ∧
        (G.pullback e).toPredimension.IsGloballyDClosed c := by
  classical
  intro s
  obtain ⟨c, hSc, hc⟩ := hCover (s.image e)
  let t : Finset U := c.image e.symm
  have htImage : t.image e = c := by
    simp [t, Finset.image_image, Function.comp_def]
  refine ⟨t, ?_, ?_⟩
  · intro x hx
    apply Finset.mem_image.mpr
    refine ⟨e x, hSc ?_, e.symm_apply_apply x⟩
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · apply (G.globallyDClosed_pullback_iff e t).2
    simpa only [htImage] using hc

/-- Every finite growth inequality transfers exactly, without
strengthening the growth bound or changing any natural cardinality. -/
theorem finiteGrowth_pullback
    (G : GraphOn V) (e : U ≃ V) (F : ℕ → ℝ)
    (hGrowth : ∀ s : Finset V, F s.card ≤ (G.predim s : ℝ)) :
    ∀ s : Finset U,
      F s.card ≤ ((G.pullback e).predim s : ℝ) := by
  classical
  intro s
  have hAdj : ∀ x y : U,
      (G.pullback e).adj x y ↔ G.adj (e x) (e y) :=
    fun _ _ => Iff.rfl
  have h := hGrowth (s.image e)
  rw [Finset.card_image_of_injective s e.injective,
      (G.pullback e).predim_image G e e.injective hAdj s] at h
  exact h

end GraphOn
end BigHrushovski
