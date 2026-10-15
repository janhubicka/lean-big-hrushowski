import BigHrushovski.InducedEmbedding
import BigHrushovski.CFMinimalDClosed
import BigHrushovski.CFDClosedHull

/-!
# Strict d-closure under finite induced graph embeddings

An induced injection preserves all finite predimension values. In
particular it preserves and reflects strict d-closedness of the
whole interval between two finite vertex sets, minimal d-closed
steps, and their least d-closed generated hulls.

The result is valid for arbitrary finite induced embeddings into
possibly infinite graphs, provided the ambient target set is exactly
the image of the source endpoint. It is not a claim that the image
is d-closed in a larger target outside this finite interval.

These statements will be used to transport the certified C_F local
support under the increasing ordered normalization of new blocks.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*}
variable [DecidableEq U] [DecidableEq V]

/-- Exact strict d-closedness invariance for every finite induced
embedding, with the target ambient set restricted to the image. -/
theorem dClosed_image_iff
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v))
    (a b : Finset U) (hab : a ⊆ b) :
    H.toPredimension.IsDClosed (a.image f) (b.image f) ↔
      G.toPredimension.IsDClosed a b := by
  classical
  constructor
  · intro hImg
    refine ⟨hab, ?_⟩
    intro c hac hcNe hcb
    have hImageNe : c.image f ≠ a.image f := by
      intro hEq
      exact hcNe ((Finset.image_injective hf) hEq)
    have hStrict := hImg.2 (c.image f)
      (Finset.image_mono f hac) hImageNe (Finset.image_mono f hcb)
    change H.predim (a.image f) < H.predim (c.image f) at hStrict
    rw [G.predim_image H f hf hAdj a,
      G.predim_image H f hf hAdj c] at hStrict
    exact hStrict
  · intro hSrc
    refine ⟨Finset.image_mono f hSrc.1, ?_⟩
    intro c hAc hcNe hCb
    let t : Finset U := b.filter (fun u => f u ∈ c)
    have htB : t ⊆ b := by
      intro u hu
      exact (Finset.mem_filter.mp hu).1
    have htImage : t.image f = c :=
      finite_image_preimage_within f b c hCb
    have hAT : a ⊆ t := by
      intro u hu
      have hFu : f u ∈ a.image f :=
        Finset.mem_image.mpr ⟨u, hu, rfl⟩
      exact Finset.mem_filter.mpr ⟨hab hu, hAc hFu⟩
    have htNe : t ≠ a := by
      intro hEq
      apply hcNe
      calc
        c = t.image f := htImage.symm
        _ = a.image f := by rw [hEq]
    have hStrict := hSrc.2 t hAT htNe htB
    change G.predim a < G.predim t at hStrict
    change H.predim (a.image f) < H.predim c
    rw [← htImage, G.predim_image H f hf hAdj a,
      G.predim_image H f hf hAdj t]
    exact hStrict

/-- Minimal strict d-closed steps are exactly invariant under
finite induced embeddings when the entire endpoint is imaged. -/
theorem minimalDClosedStep_image_iff
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v))
    (a b : Finset U) (hab : a ⊆ b) :
    H.toPredimension.IsMinimalDClosedStep (a.image f) (b.image f) ↔
      G.toPredimension.IsMinimalDClosedStep a b := by
  classical
  constructor
  · intro hImg
    have hEndpoint : G.toPredimension.IsDClosed a b :=
      (G.dClosed_image_iff H f hf hAdj a b hab).mp hImg.1
    have hNe : a ≠ b := by
      intro hEq
      exact hImg.2.1 (by rw [hEq])
    refine ⟨hEndpoint, hNe, ?_⟩
    intro z haz hzb hzClosed
    have hZImgClosed : H.toPredimension.IsDClosed
        (z.image f) (b.image f) :=
      (G.dClosed_image_iff H f hf hAdj z b hzb).mpr hzClosed
    rcases hImg.2.2 (z.image f)
      (Finset.image_mono f haz) (Finset.image_mono f hzb)
      hZImgClosed with hEq | hEq
    · left
      exact (Finset.image_injective hf) hEq
    · right
      exact (Finset.image_injective hf) hEq
  · intro hSrc
    have hEndpoint : H.toPredimension.IsDClosed
        (a.image f) (b.image f) :=
      (G.dClosed_image_iff H f hf hAdj a b hab).mpr hSrc.1
    have hNe : a.image f ≠ b.image f := by
      intro hEq
      exact hSrc.2.1 ((Finset.image_injective hf) hEq)
    refine ⟨hEndpoint, hNe, ?_⟩
    intro z hAz hzB hzClosed
    let t : Finset U := b.filter (fun u => f u ∈ z)
    have htB : t ⊆ b := by
      intro u hu
      exact (Finset.mem_filter.mp hu).1
    have htImage : t.image f = z :=
      finite_image_preimage_within f b z hzB
    have hAT : a ⊆ t := by
      intro u hu
      have hFu : f u ∈ a.image f :=
        Finset.mem_image.mpr ⟨u, hu, rfl⟩
      exact Finset.mem_filter.mpr ⟨hab hu, hAz hFu⟩
    have htClosed : G.toPredimension.IsDClosed t b := by
      apply (G.dClosed_image_iff H f hf hAdj t b htB).mp
      rw [htImage]
      exact hzClosed
    rcases hSrc.2.2 t hAT htB htClosed with hEq | hEq
    · left
      calc
        z = t.image f := htImage.symm
        _ = a.image f := by rw [hEq]
    · right
      calc
        z = t.image f := htImage.symm
        _ = b.image f := by rw [hEq]

/-- Least finite strict d-closed generated hulls commute with
any induced injection, when both are taken in corresponding
finite ambient endpoints. -/
theorem dClosedHull_image
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ u v : U, G.adj u v ↔ H.adj (f u) (f v))
    (s b : Finset U) (hsb : s ⊆ b) :
    (G.toPredimension.dClosedHull s b).image f =
      H.toPredimension.dClosedHull (s.image f) (b.image f) := by
  classical
  let dG := G.toPredimension
  let dH := H.toPredimension
  have hGH : dG.IsDClosed (dG.dClosedHull s b) b :=
    dG.dClosedHull_dclosed s b
  have hGImg : dH.IsDClosed
      ((dG.dClosedHull s b).image f) (b.image f) :=
    (G.dClosed_image_iff H f hf hAdj
      (dG.dClosedHull s b) b hGH.1).mpr hGH
  have hSImg : s.image f ⊆ (dG.dClosedHull s b).image f :=
    Finset.image_mono f (dG.subset_dClosedHull hsb)
  have hRightToLeft :
      dH.dClosedHull (s.image f) (b.image f) ⊆
        (dG.dClosedHull s b).image f :=
    dH.dClosedHull_least hSImg hGImg
  let t : Finset U := b.filter (fun u =>
    f u ∈ dH.dClosedHull (s.image f) (b.image f))
  have hHClosed : dH.IsDClosed
      (dH.dClosedHull (s.image f) (b.image f)) (b.image f) :=
    dH.dClosedHull_dclosed (s.image f) (b.image f)
  have htImage : t.image f =
      dH.dClosedHull (s.image f) (b.image f) :=
    finite_image_preimage_within f b
      (dH.dClosedHull (s.image f) (b.image f)) hHClosed.1
  have htB : t ⊆ b := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have hST : s ⊆ t := by
    intro u hu
    have hFu : f u ∈ s.image f :=
      Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hS : s.image f ⊆
        dH.dClosedHull (s.image f) (b.image f) :=
      dH.subset_dClosedHull (Finset.image_mono f hsb)
    exact Finset.mem_filter.mpr ⟨hsb hu, hS hFu⟩
  have htClosed : dG.IsDClosed t b := by
    apply (G.dClosed_image_iff H f hf hAdj t b htB).mp
    rw [htImage]
    exact hHClosed
  have hGSubT : dG.dClosedHull s b ⊆ t :=
    dG.dClosedHull_least hST htClosed
  have hLeftToRight :
      (dG.dClosedHull s b).image f ⊆
        dH.dClosedHull (s.image f) (b.image f) := by
    rw [← htImage]
    exact Finset.image_mono f hGSubT
  exact le_antisymm hLeftToRight hRightToLeft

end GraphOn
end BigHrushovski
