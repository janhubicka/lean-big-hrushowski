import BigHrushovski.StrictStrongClosure
import BigHrushovski.InducedEmbedding
import BigHrushovski.SpanNormalization

/-!
# Uniqueness of the finite induced strong-closure diagram over generators

Let C be the least finite globally strong closure of X in the
countable Hrushovski generic. An arbitrary induced copy of C into
the generic which fixes every vertex of X has image exactly C.

The argument uses the already verified finite-subset predimension
and cardinality invariants of injective induced graph maps, and
the strict minimality of C among finite supersets of X.
The conclusion concerns the *vertex set* of a finite induced copy,
not its pointwise identity on C: internal automorphisms may permute
the finitely many vertices of C over X.

This is the combinatorial half of showing C ⊆ acl(X).
A first-order finite-diagram formula and the converse infinite
conjugate argument remain separate model-theoretic obligations.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every induced copy of the finite strong closure of s that fixes s
has precisely the original closure as its image; no new vertex outside
the closure can occur in such a copy. -/
theorem genericStrongClosure_induced_copy_image
    (s : Finset ℕ)
    (f : {v : ℕ // v ∈ genericStrongClosure s} → ℕ)
    (hf : Function.Injective f)
    (hInduced : ∀ x y : {v : ℕ // v ∈ genericStrongClosure s},
      genericTwoSparseGraph.adj x.val y.val ↔
        genericTwoSparseGraph.adj (f x) (f y))
    (hFix : ∀ x : {v : ℕ // v ∈ genericStrongClosure s},
      x.val ∈ s → f x = x.val) :
    (Finset.univ :
      Finset {v : ℕ // v ∈ genericStrongClosure s}).image f =
        genericStrongClosure s := by
  classical
  let c := genericStrongClosure s
  let A := {v : ℕ // v ∈ c}
  have hsc : s ⊆ c := subset_genericStrongClosure s
  have hValImage :
      (Finset.univ : Finset A).image (Subtype.val : A → ℕ) = c := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact x.property
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have hContains :
      s ⊆ (Finset.univ : Finset A).image f := by
    intro z hz
    exact Finset.mem_image.mpr
      ⟨⟨z, hsc hz⟩, Finset.mem_univ _, hFix ⟨z, hsc hz⟩ hz⟩
  have hCard :
      ((Finset.univ : Finset A).image f).card = c.card := by
    calc
      ((Finset.univ : Finset A).image f).card =
          (Finset.univ : Finset A).card :=
        Finset.card_image_of_injective _ hf
      _ = ((Finset.univ : Finset A).image (Subtype.val : A → ℕ)).card :=
        (Finset.card_image_of_injective _
          (Subtype.val_injective : Function.Injective (Subtype.val : A → ℕ))).symm
      _ = c.card := by rw [hValImage]
  let H : GraphOn A :=
    genericTwoSparseGraph.pullback (Subtype.val : A → ℕ)
  have hδf :
      genericTwoSparseGraph.predim
        ((Finset.univ : Finset A).image f) =
        H.predim (Finset.univ : Finset A) :=
    H.predim_image genericTwoSparseGraph f hf hInduced Finset.univ
  have hδval :
      genericTwoSparseGraph.predim c =
        H.predim (Finset.univ : Finset A) := by
    have h := H.predim_image genericTwoSparseGraph
      (Subtype.val : A → ℕ) Subtype.val_injective
      (fun _ _ => Iff.rfl) (Finset.univ : Finset A)
    rw [hValImage] at h
    exact h
  have hδ :
      genericTwoSparseGraph.predim
        ((Finset.univ : Finset A).image f) =
        genericTwoSparseGraph.predim c :=
    hδf.trans hδval.symm
  exact genericStrongClosure_unique_equal_pattern
    s ((Finset.univ : Finset A).image f) hContains hCard hδ

end FiniteCatalogue
end BigHrushovski
