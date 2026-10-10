import BigHrushovski.UnlabelledExtension

/-!
# Universality of a sparse graph with the strong extension property

The extension property already established for arbitrary finite strong
diagrams implies the universality clause of the strong Fraisse limit,
once the ambient graph has nonnegative predimension on every finite
set. The empty finite subgraph is globally strong, and each finite
2-sparse graph is a strong extension of this empty base.

This is a conditional statement about arbitrary ambient graphs; it
does not assume a particular countable generic construction.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- In a graph with nonnegative predimension on every finite subset,
the empty set is globally self-sufficient. -/
theorem empty_globallyStrong_of_sparse
    (M : GraphOn ℕ)
    (hSparse : ∀ s : Finset ℕ, 0 ≤ M.predim s) :
    M.toPredimension.IsGloballyStrong ∅ := by
  intro b _
  apply M.empty_strong_of_twoSparse
  intro s _
  exact hSparse s

/-- Every finite 2-sparse graph has an induced globally strong copy
in any countable 2-sparse graph with the strong extension property. -/
theorem exists_globallyStrong_copy
    (M : GraphOn ℕ)
    (hSparse : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hExt : HasStrongExtensionProperty M)
    {B : Type*} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    (hH : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ g : B → ℕ,
      Function.Injective g ∧
      (∀ x y : B, H.adj x y ↔ M.adj (g x) (g y)) ∧
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image g) := by
  classical
  let Gempty : GraphOn Empty := H.pullback (fun x : Empty => Empty.elim x)
  let i : Empty → B := Empty.elim
  let f : Empty → ℕ := Empty.elim
  have hEmptySparse :
      Gempty.IsTwoSparse (Finset.univ : Finset Empty) := by
    have hUniv : (Finset.univ : Finset Empty) = ∅ := by
      simp
    rw [hUniv]
    exact Gempty.twoSparse_empty
  have hBaseStrong :
      H.toPredimension.IsStrong
        ((Finset.univ : Finset Empty).image i)
        (Finset.univ : Finset B) := by
    have hImage : ((Finset.univ : Finset Empty).image i) =
        (∅ : Finset B) := by
      simp
    rw [hImage]
    exact H.empty_strong_of_twoSparse hH
  have hAmbientEmpty :
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset Empty).image f) := by
    have hImage : ((Finset.univ : Finset Empty).image f) =
        (∅ : Finset ℕ) := by
      simp
    rw [hImage]
    exact empty_globallyStrong_of_sparse M hSparse
  obtain ⟨g, hg, hInduced, _, hStrong⟩ :=
    arbitrary_finite_strong_extension M hExt
      Gempty H i
      (by intro x; exact Empty.elim x)
      (by intro x; exact Empty.elim x)
      hEmptySparse hH hBaseStrong f
      (by intro x; exact Empty.elim x)
      (by intro x; exact Empty.elim x)
      hAmbientEmpty
  exact ⟨g, hg, hInduced, hStrong⟩

end FiniteCatalogue
end BigHrushovski
