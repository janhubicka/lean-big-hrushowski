import BigHrushovski.C0LocalFreeConverse
import BigHrushovski.InducedEmbedding

/-!
# Minimal strong steps are invariant under induced finite graph embeddings

The existing strong_image_iff theorem transfers self-sufficiency, but
not by itself *minimality*: to rule out a new intermediate strong
subgraph of the image one must pull the entire intermediate vertex set
back through the induced embedding, including nonedges.

This module proves the exact equivalence. The source graph may have an
infinite vertex type, but all subsets in the statement are finite.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

theorem minimalStrongStep_image_iff
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (a b : Finset U) (hab : a ⊆ b) :
    H.toPredimension.IsMinimalStrongStep (a.image f) (b.image f) ↔
      G.toPredimension.IsMinimalStrongStep a b := by
  classical
  constructor
  · intro himg
    have hStrong : G.toPredimension.IsStrong a b :=
      (G.strong_image_iff H f hf hAdj a b hab).mp himg.1
    have hProper : a ≠ b := by
      intro heq
      exact himg.2.1 (by rw [heq])
    refine ⟨hStrong, hProper, ?_⟩
    intro z haz hzb hzStrong
    have hImageStrong :
        H.toPredimension.IsStrong (z.image f) (b.image f) :=
      (G.strong_image_iff H f hf hAdj z b hzb).mpr hzStrong
    rcases himg.2.2 (z.image f)
      (Finset.image_mono f haz) (Finset.image_mono f hzb)
      hImageStrong with hZa | hZb
    · exact Or.inl (Finset.image_injective hf hZa)
    · exact Or.inr (Finset.image_injective hf hZb)
  · intro hsrc
    have hStrong :
        H.toPredimension.IsStrong (a.image f) (b.image f) :=
      (G.strong_image_iff H f hf hAdj a b hab).mpr hsrc.1
    have hProper : a.image f ≠ b.image f := by
      intro hEq
      exact hsrc.2.1 (Finset.image_injective hf hEq)
    refine ⟨hStrong, hProper, ?_⟩
    intro z haz hzb hzStrong
    let t : Finset U := b.filter (fun u => f u ∈ z)
    have htSub : t ⊆ b := by
      intro u hu
      exact (Finset.mem_filter.mp hu).1
    have haSub : a ⊆ t := by
      intro u hu
      exact Finset.mem_filter.mpr
        ⟨hab hu, haz (Finset.mem_image.mpr ⟨u, hu, rfl⟩)⟩
    have htImage : t.image f = z :=
      finite_image_preimage_within f b z hzb
    have htStrong :
        G.toPredimension.IsStrong t b := by
      apply (G.strong_image_iff H f hf hAdj t b htSub).mp
      rw [htImage]
      exact hzStrong
    rcases hsrc.2.2 t haSub htSub htStrong with hTa | hTb
    · left
      calc
        z = t.image f := htImage.symm
        _ = a.image f := by rw [hTa]
    · right
      calc
        z = t.image f := htImage.symm
        _ = b.image f := by rw [hTb]

end GraphOn
end BigHrushovski
