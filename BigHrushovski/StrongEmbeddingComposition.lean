import BigHrushovski.InducedEmbedding

/-!
# Composition of finite induced strong graph embeddings

In a recursive strong Fraïssé construction, a finite extension request
may be answered in an intermediate graph and then the intermediate
graph enlarged again to force growth. The original strong base and
the answering copy must remain strong in the final stage.

This is transitivity of finite relative strongness, combined with the
already-verified exact transport of strongness under induced injective
graph embeddings. The result is valid for any two finite graph stages
and does not assert the existence of the countable limit.
-/

namespace BigHrushovski
namespace GraphOn

/-- A strong finite image remains strong after another induced strong
embedding. In particular both old and newly answered strong copies
survive the forced-growth extension of a finite stage. -/
theorem strong_image_trans_of_induced
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (G : GraphOn B) (H : GraphOn C)
    (f : A → B) (g : B → C)
    (hg : Function.Injective g)
    (hInduced : ∀ x y : B,
      G.adj x y ↔ H.adj (g x) (g y))
    (hStrongF : G.toPredimension.IsStrong
      ((Finset.univ : Finset A).image f)
      (Finset.univ : Finset B))
    (hStrongG : H.toPredimension.IsStrong
      ((Finset.univ : Finset B).image g)
      (Finset.univ : Finset C)) :
    H.toPredimension.IsStrong
      ((Finset.univ : Finset A).image (g ∘ f))
      (Finset.univ : Finset C) := by
  classical
  have hLocal :
      H.toPredimension.IsStrong
        (((Finset.univ : Finset A).image f).image g)
        ((Finset.univ : Finset B).image g) :=
    (G.strong_image_iff H g hg hInduced
      ((Finset.univ : Finset A).image f)
      (Finset.univ : Finset B)
      (Finset.subset_univ _)).mpr hStrongF
  have hAll := H.toPredimension.strong_trans hLocal hStrongG
  simpa only [Finset.image_image] using hAll

end GraphOn
end BigHrushovski
