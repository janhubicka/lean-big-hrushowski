import BigHrushovski.GenericStrongClosure
import BigHrushovski.InducedEmbedding

/-!
# Equivariance of finite strong closure under induced automorphisms

An induced automorphism of a graph preserves finite predimension,
and therefore the family of finite globally strong vertex sets.
For the countable two-sparse Hrushovski generic, the least finite
globally strong closure is consequently equivariant.

This is a closure-naturality theorem in the pure graph presentation.
It is a prerequisite for analysing orbits over finite sets and the
relationship with model-theoretic algebraic closure. Finite orbits
alone are not asserted to imply algebraicity without an appropriate
definability argument.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V]

/-- An induced automorphism sends finite globally self-sufficient
subgraphs to finite globally self-sufficient subgraphs. -/
theorem globallyStrong_image_of_equiv
    (G : GraphOn V) (e : V ≃ V)
    (hAdj : ∀ x y : V, G.adj x y ↔ G.adj (e x) (e y))
    {a : Finset V}
    (ha : G.toPredimension.IsGloballyStrong a) :
    G.toPredimension.IsGloballyStrong (a.image e) := by
  classical
  intro b hab
  let c : Finset V := b.image e.symm
  have hac : a ⊆ c := by
    intro x hx
    have hb : e x ∈ b :=
      hab (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    exact Finset.mem_image.mpr
      ⟨e x, hb, e.symm_apply_apply x⟩
  have hStrong := ha c hac
  have hTrans :=
    (G.strong_image_iff G e e.injective hAdj a c hac).mpr hStrong
  have hcImage : c.image e = b := by
    unfold c
    rw [Finset.image_image]
    have hComp : (e : V → V) ∘ (e.symm : V → V) = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hComp]
    simp
  rw [hcImage] at hTrans
  exact hTrans

end GraphOn

namespace FiniteCatalogue

/-- The strong closure of a finite vertex set commutes with every
induced automorphism of the concrete countable generic graph. -/
theorem genericStrongClosure_equivariant
    (e : ℕ ≃ ℕ)
    (hAdj : ∀ x y : ℕ,
      genericTwoSparseGraph.adj x y ↔
        genericTwoSparseGraph.adj (e x) (e y))
    (s : Finset ℕ) :
    genericStrongClosure (s.image e) =
      (genericStrongClosure s).image e := by
  classical
  have hImageGlobal :
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        ((genericStrongClosure s).image e) :=
    genericTwoSparseGraph.globallyStrong_image_of_equiv e hAdj
      (genericStrongClosure_global s)
  have hImageSource :
      s.image e ⊆ (genericStrongClosure s).image e :=
    Finset.image_mono e (subset_genericStrongClosure s)
  have hForward :
      genericStrongClosure (s.image e) ⊆
        (genericStrongClosure s).image e :=
    genericStrongClosure_least (s.image e)
      ((genericStrongClosure s).image e)
      hImageGlobal hImageSource
  have hAdjInv : ∀ x y : ℕ,
      genericTwoSparseGraph.adj x y ↔
        genericTwoSparseGraph.adj (e.symm x) (e.symm y) := by
    intro x y
    simpa using (hAdj (e.symm x) (e.symm y)).symm
  have hInverseGlobal :
      genericTwoSparseGraph.toPredimension.IsGloballyStrong
        ((genericStrongClosure (s.image e)).image e.symm) :=
    genericTwoSparseGraph.globallyStrong_image_of_equiv
      e.symm hAdjInv (genericStrongClosure_global (s.image e))
  have hInverseSource :
      s ⊆ (genericStrongClosure (s.image e)).image e.symm := by
    intro x hx
    have hxImage : e x ∈ s.image e :=
      Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hxCl : e x ∈ genericStrongClosure (s.image e) :=
      (subset_genericStrongClosure (s.image e)) hxImage
    exact Finset.mem_image.mpr
      ⟨e x, hxCl, e.symm_apply_apply x⟩
  have hReverseBefore :
      genericStrongClosure s ⊆
        (genericStrongClosure (s.image e)).image e.symm :=
    genericStrongClosure_least s
      ((genericStrongClosure (s.image e)).image e.symm)
      hInverseGlobal hInverseSource
  have hReverse := Finset.image_mono e hReverseBefore
  have hImageInverse :
      ((genericStrongClosure (s.image e)).image e.symm).image e =
        genericStrongClosure (s.image e) := by
    rw [Finset.image_image]
    have hComp : (e : ℕ → ℕ) ∘ (e.symm : ℕ → ℕ) = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hComp]
    simp
  rw [hImageInverse] at hReverse
  exact Finset.Subset.antisymm hForward hReverse

end FiniteCatalogue
end BigHrushovski
