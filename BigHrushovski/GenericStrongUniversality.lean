import BigHrushovski.StrongAgeUniversality
import BigHrushovski.GenericFraisseConstruction

/-!
# Universality of the constructed countable strong generic graph

The independently verified finite strong-age universality criterion
requires a two-sparse countable graph with the labelled strong extension
property. Both hypotheses now hold for the concrete graph built by
fair finite recursion in `GenericFraisseConstruction.lean`.

This proves that every finite two-sparse graph, on an arbitrary finite
vertex type, embeds with globally strong induced image into that graph.
Homogeneity and uniqueness of the strong Fraïssé limit require the
separate back-and-forth argument recorded in
`docs/STRONG_FRAISSE_IDENTIFICATION.md`.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every finite two-sparse graph has a globally strong induced copy
in the countable graph constructed by fair strong recursion. -/
theorem genericTwoSparseGraph_strongUniversal
    {B : Type*} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    (hH : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ g : B → ℕ,
      Function.Injective g ∧
      (∀ x y : B, H.adj x y ↔
        genericTwoSparseGraph.adj (g x) (g y)) ∧
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image g) :=
  exists_globallyStrong_copy genericTwoSparseGraph
    genericTwoSparseGraph_sparse
    genericTwoSparseGraph_strongExtension H hH

end FiniteCatalogue
end BigHrushovski
