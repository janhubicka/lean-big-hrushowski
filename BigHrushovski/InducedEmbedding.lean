import BigHrushovski.TaggedAmalgam

/-!
# Predimension under an induced graph embedding

For an injective map preserving and reflecting adjacency, the finite
induced edges of the image of any finite set correspond exactly to the
images of its original edges. Consequently predimension is unchanged.

The result is stated for graphs on arbitrary types, with no global
finiteness hypothesis. It will be used to transfer strongness to the
canonical embeddings of the tagged free graph amalgam.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Induced adjacency and an injective map preserve the assertion that
a finite vertex set is an unordered graph edge. -/
theorem isEdge_image_iff (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (e : Finset U) :
    G.IsEdge e ↔ H.IsEdge (e.image f) := by
  have hCard : (e.image f).card = e.card :=
    Finset.card_image_of_injective e hf
  constructor
  · rintro ⟨heCard, x, hx, y, hy, hxy⟩
    refine ⟨by omega, f x, ?_, f y, ?_, (hAdj x y).mp hxy⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  · rintro ⟨heCard, x, hx, y, hy, hxy⟩
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy
    have huv : G.adj u v := (hAdj u v).mpr (by
      rw [hux, hvy]
      exact hxy)
    exact ⟨by omega, u, hu, v, hv, huv⟩

/-- Edges on the image of a finite set are exactly the images of its
original edges. No extra edge can appear by inducedness. -/
theorem edgesWithin_image (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (s : Finset U) :
    H.edgesWithin (s.image f) =
      (G.edgesWithin s).image (fun e => e.image f) := by
  classical
  ext edge
  constructor
  · intro hEdge
    have hSub : edge ⊆ s.image f :=
      ((H.mem_edgesWithin_iff (s.image f) edge).mp hEdge).1
    let t : Finset U := s.filter (fun u => f u ∈ edge)
    have htImage : t.image f = edge := by
      ext z
      constructor
      · intro hz
        obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
        have huEdge : f u ∈ edge := (Finset.mem_filter.mp hu).2
        rw [huz] at huEdge
        exact huEdge
      · intro hz
        obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp (hSub hz)
        refine Finset.mem_image.mpr ⟨u, ?_, huz⟩
        exact Finset.mem_filter.mpr ⟨hu, by rw [huz]; exact hz⟩
    have hTedge : G.IsEdge t := by
      apply (G.isEdge_image_iff H f hf hAdj t).mpr
      rw [htImage]
      exact ((H.mem_edgesWithin_iff (s.image f) edge).mp hEdge).2
    have ht : t ∈ G.edgesWithin s :=
      (G.mem_edgesWithin_iff s t).mpr
        ⟨by intro u hu; exact (Finset.mem_filter.mp hu).1, hTedge⟩
    exact Finset.mem_image.mpr ⟨t, ht, htImage⟩
  · intro h
    obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp h
    obtain ⟨htSub, htEdge⟩ := (G.mem_edgesWithin_iff s t).mp ht
    have htImageSub : t.image f ⊆ s.image f :=
      Finset.image_mono htSub
    have htImageEdge : H.IsEdge (t.image f) :=
      (G.isEdge_image_iff H f hf hAdj t).mp htEdge
    rw [← hte]
    exact (H.mem_edgesWithin_iff (s.image f) (t.image f)).mpr
      ⟨htImageSub, htImageEdge⟩

/-- The edge count is invariant under an induced injective graph map. -/
theorem card_edgesWithin_image (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (s : Finset U) :
    (H.edgesWithin (s.image f)).card =
      (G.edgesWithin s).card := by
  rw [G.edgesWithin_image H f hf hAdj s]
  exact Finset.card_image_of_injective (G.edgesWithin s)
    (Finset.image_injective hf)

/-- Graph predimension is invariant under induced injective embeddings. -/
theorem predim_image (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (hf : Function.Injective f)
    (hAdj : ∀ x y : U, G.adj x y ↔ H.adj (f x) (f y))
    (s : Finset U) :
    H.predim (s.image f) = G.predim s := by
  have hVertices : (s.image f).card = s.card :=
    Finset.card_image_of_injective s hf
  have hEdges := G.card_edgesWithin_image H f hf hAdj s
  unfold predim
  omega

end GraphOn
end BigHrushovski
