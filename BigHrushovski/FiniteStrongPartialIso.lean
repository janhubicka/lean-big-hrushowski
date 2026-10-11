import BigHrushovski.StrongAgeUniversality

/-!
# Finite strong partial isomorphisms

A finite strong partial isomorphism between graphs M and N is an
equivalence between finite globally self-sufficient induced subgraphs.
The underlying vertex subsets need not be initial segments, and no
bound on the size of their strong closures is assumed.

The symmetric inverse and the empty initial partial isomorphism
provide the basic data for the strong back-and-forth recursion.
The local forth/back extension theorems are developed separately.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- An induced graph isomorphism between finite globally strong
subgraphs of two potentially different countable graphs. -/
structure FiniteStrongPartialIso (M N : GraphOn ℕ) where
  source : Finset ℕ
  target : Finset ℕ
  equiv : {x : ℕ // x ∈ source} ≃ {y : ℕ // y ∈ target}
  source_global : M.toPredimension.IsGloballyStrong source
  target_global : N.toPredimension.IsGloballyStrong target
  induced : ∀ x y : {x : ℕ // x ∈ source},
    M.adj x.val y.val ↔ N.adj (equiv x).val (equiv y).val

namespace FiniteStrongPartialIso

variable {M N : GraphOn ℕ}

/-- Reverse an induced finite strong partial isomorphism. -/
noncomputable def symm (p : FiniteStrongPartialIso M N) :
    FiniteStrongPartialIso N M where
  source := p.target
  target := p.source
  equiv := p.equiv.symm
  source_global := p.target_global
  target_global := p.source_global
  induced := by
    intro x y
    simpa using (p.induced (p.equiv.symm x) (p.equiv.symm y)).symm

/-- The numerical range of the finite equivalence is exactly its
declared finite target; no unwanted or missing values remain. -/
theorem image_equiv_eq_target (p : FiniteStrongPartialIso M N) :
    (Finset.univ : Finset {x : ℕ // x ∈ p.source}).image
      (fun x => (p.equiv x).val) = p.target := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    rw [← hx]
    exact (p.equiv x).property
  · intro hz
    refine Finset.mem_image.mpr
      ⟨p.equiv.symm ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
    simp

/-- The empty map is a globally strong induced partial isomorphism
between any two 2-sparse countable graphs. -/
noncomputable def empty (M N : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s) :
    FiniteStrongPartialIso M N where
  source := ∅
  target := ∅
  equiv := Equiv.refl _
  source_global := empty_globallyStrong_of_sparse M hSparseM
  target_global := empty_globallyStrong_of_sparse N hSparseN
  induced := by
    intro x
    exact False.elim (Finset.not_mem_empty x.val x.property)

end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
