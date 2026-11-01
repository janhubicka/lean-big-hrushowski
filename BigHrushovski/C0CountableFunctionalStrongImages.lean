import BigHrushovski.C0CountableCanonicalStages
import BigHrushovski.InducedEmbedding

/-!
# Strong images of finite canonical functional C₀ structures

Suppose the countable graph N carries a complete unary closure C
whose finite induced stages have exact canonical component presentations.
A finite canonical functional embedding f:K→N preserves complete
C-values, not just graph adjacency. Therefore its finite image is
C-closed, hence globally strong. In particular every graph-strong
finite substructure of K has globally strong image in N.

This is the crucial strongness transfer needed when a finite strong
graph span is first lifted to a functional extension, then realized
in a countable functional Fraïssé structure. It does not assume that
arbitrary graph-strong sets are already C-closed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact preservation of complete unary values automatically makes
the full finite embedding image closed under the ambient function.
Neither a separate closure premise nor injectivity is needed for
this elementary inclusion statement. -/
theorem completeFunctionalImage_closed
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (K : GraphOn V) {m : ℕ} (κ : V → Fin m)
    (f : V → ℕ)
    (hValues : ∀ u : V,
      C (f u) = (canonicalValue K κ u).image f) :
    N.IsClosedUnderValues C
      ((Finset.univ : Finset V).image f) := by
  intro x hx y hy
  obtain ⟨u, _, hEq⟩ := Finset.mem_image.mp hx
  rw [← hEq, hValues u] at hy
  obtain ⟨v, _, hvEq⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr
    ⟨v, Finset.mem_univ _, hvEq⟩

/-- The image of a finite strong graph set inside a finite canonical
functional structure is globally strong in a countable functional
presentation, provided its finite stages agree on the *complete*
canonical unary values and the given embedding preserves them. -/
theorem globallyStrong_image_of_completeFunctionalEmbedding
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (K : GraphOn V) {m : ℕ} (κ : V → Fin m)
    (f : V → ℕ)
    (hf : Function.Injective f)
    (hAdj : ∀ x y : V,
      K.adj x y ↔ N.adj (f x) (f y))
    (hValues : ∀ u : V,
      C (f u) = (canonicalValue K κ u).image f)
    (a : Finset V)
    (hStrong : K.toPredimension.IsStrong a Finset.univ) :
    N.toPredimension.IsGloballyStrong (a.image f) := by
  have hClosed :
      N.IsClosedUnderValues C
        ((Finset.univ : Finset V).image f) :=
    completeFunctionalImage_closed N C K κ f hValues
  have hWholeGlobal : N.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset V).image f) :=
    globallyStrong_of_closed_stages N C stage hCover
      (localStrong_of_canonicalFiniteStages N C stage hStage)
      ((Finset.univ : Finset V).image f) hClosed
  have hLocal : N.toPredimension.IsStrong
      (a.image f) ((Finset.univ : Finset V).image f) :=
    (K.strong_image_iff N f hf hAdj
      a Finset.univ (Finset.subset_univ a)).mpr hStrong
  exact N.toPredimension.globallyStrong_of_strong_in_global
    hLocal hWholeGlobal

end FiniteC0
end BigHrushovski
