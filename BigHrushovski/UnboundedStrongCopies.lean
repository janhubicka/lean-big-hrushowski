import BigHrushovski.DisjointStrongCopies
import BigHrushovski.GenericStrongClosure

/-!
# Strong copies over the base avoiding arbitrary finite forbidden sets

The disjoint-strong-copy theorem places a finite strong extension of
C outside a prescribed finite globally strong B. Every finite
forbidden set F can be included in such a B by the verified finite
strong-cover property of the countable Hrushovski generic.

Consequently, for every finite F, there is a globally strong induced
copy of the finite extension over the *literal* base C whose new
vertices avoid F. This provides the finitary unboundedness needed
to construct infinitely many conjugates over C.

We do not yet state the model-theoretic algebraic-closure conclusion
or formalize the corresponding automorphism orbit.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A finite strong extension of a globally strong finite base in the
constructed generic has a globally strong induced copy over that base
with all additional vertices outside any given finite forbidden set. -/
theorem generic_exists_strong_copy_avoiding
    (c forbidden : Finset ℕ)
    (hc : genericTwoSparseGraph.toPredimension.IsGloballyStrong c)
    {D : Type*} [Fintype D] [DecidableEq D]
    (H : GraphOn D)
    (j : {p : ℕ // p ∈ c} → D)
    (hj : Function.Injective j)
    (hInduced : ∀ p q : {p : ℕ // p ∈ c},
      H.adj (j p) (j q) ↔
        genericTwoSparseGraph.adj p.val q.val)
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset D))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset {p : ℕ // p ∈ c}).image j)
      (Finset.univ : Finset D)) :
    ∃ g : D → ℕ,
      Function.Injective g ∧
      (∀ x y : D,
        H.adj x y ↔ genericTwoSparseGraph.adj (g x) (g y)) ∧
      (∀ p : {p : ℕ // p ∈ c}, g (j p) = p.val) ∧
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset D).image g) ∧
      (∀ x : D, g x ∈ forbidden →
        ∃ p : {p : ℕ // p ∈ c}, x = j p) := by
  classical
  obtain ⟨b, hContains, hb⟩ :=
    genericTwoSparseGraph_finiteStrongCover.exists_container
      (c ∪ forbidden)
  have hcb : c ⊆ b :=
    Finset.subset_union_left.trans hContains
  obtain ⟨g, hg, hAdj, hFix, hGlobal, hAvoid⟩ :=
    exists_disjoint_strong_copy
      genericTwoSparseGraph genericTwoSparseGraph_sparse
      genericTwoSparseGraph_strongExtension
      c b hcb hc hb H j hj hInduced hSparseH hStrongH
  refine ⟨g, hg, hAdj, hFix, hGlobal, ?_⟩
  intro x hx
  apply hAvoid x
  exact hContains (Finset.mem_union.mpr (Or.inr hx))

end FiniteCatalogue
end BigHrushovski
