import BigHrushovski.FiniteCatalogue
import Mathlib.Data.Fintype.EquivFin

/-!
# Every finite strong embedding has a labelled diagram

The catalogue consists of strong diagrams between graphs on Fin n and
Fin m. A finite graph with an arbitrary finite vertex carrier is
equivalent to one on a suitable Fin n; induced adjacency, 2-sparsity
and self-sufficiency are preserved by that equivalence.

This module verifies that every finite strong embedding span has a
representative in the labelled catalogue. No choice of a canonical
labelling is claimed.
-/

namespace BigHrushovski
namespace FiniteCatalogue

variable {A B : Type*}
variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A finite strong induced embedding between arbitrary finite graph
carriers is represented by a labelled strong diagram. The two
equivalences provide the exact correspondence with the original
graphs and embedding. -/
theorem exists_labelled_strong_diagram
    (G : GraphOn A) (H : GraphOn B) (f : A → B)
    (hf : Function.Injective f)
    (hAdj : ∀ x y : A, G.adj x y ↔ H.adj (f x) (f y))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset A))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrong : H.toPredimension.IsStrong
      ((Finset.univ : Finset A).image f)
      (Finset.univ : Finset B)) :
    ∃ (eA : Fin (Fintype.card A) ≃ A)
      (eB : Fin (Fintype.card B) ≃ B)
      (d : StrongDiagram (Fintype.card A) (Fintype.card B)),
      (∀ x y, d.source.adj x y ↔ G.adj (eA x) (eA y)) ∧
      (∀ x y, d.target.adj x y ↔ H.adj (eB x) (eB y)) ∧
      (∀ x, eB (d.embedding x) = f (eA x)) := by
  classical
  let eA : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let eB : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let emb : Fin (Fintype.card A) → Fin (Fintype.card B) :=
    fun x => eB.symm (f (eA x))
  have hEmbInj : Function.Injective emb := by
    intro x y hxy
    apply eA.injective
    apply hf
    exact eB.symm.injective hxy
  have hInduced : ∀ x y : Fin (Fintype.card A),
      (G.pullback eA).adj x y ↔
        (H.pullback eB).adj (emb x) (emb y) := by
    intro x y
    change G.adj (eA x) (eA y) ↔
      H.adj (eB (eB.symm (f (eA x))))
        (eB (eB.symm (f (eA y))))
    simpa using hAdj (eA x) (eA y)
  have hSparseSource : (G.pullback eA).IsTwoSparse
      (Finset.univ : Finset (Fin (Fintype.card A))) := by
    have h := ((G.pullback eA).twoSparse_image_iff G
      eA eA.injective (fun _ _ => Iff.rfl)
      (Finset.univ : Finset (Fin (Fintype.card A)))).mp
    apply h
    rw [Finset.image_univ_of_surjective eA.surjective]
    exact hSparseG
  have hSparseTarget : (H.pullback eB).IsTwoSparse
      (Finset.univ : Finset (Fin (Fintype.card B))) := by
    have h := ((H.pullback eB).twoSparse_image_iff H
      eB eB.injective (fun _ _ => Iff.rfl)
      (Finset.univ : Finset (Fin (Fintype.card B)))).mp
    apply h
    rw [Finset.image_univ_of_surjective eB.surjective]
    exact hSparseH
  have hEmbImage :
      (((Finset.univ : Finset (Fin (Fintype.card A))).image emb).image eB) =
        (Finset.univ : Finset A).image f := by
    calc
      _ = (Finset.univ : Finset (Fin (Fintype.card A))).image
          (eB ∘ emb) := by rw [Finset.image_image]
      _ = (Finset.univ : Finset (Fin (Fintype.card A))).image
          (f ∘ eA) := by
            congr 1
            funext x
            simp [emb]
      _ = ((Finset.univ : Finset (Fin (Fintype.card A))).image eA).image f := by
            rw [Finset.image_image]
      _ = (Finset.univ : Finset A).image f := by
            rw [Finset.image_univ_of_surjective eA.surjective]
  have hStrongNorm : (H.pullback eB).toPredimension.IsStrong
      ((Finset.univ : Finset (Fin (Fintype.card A))).image emb)
      (Finset.univ : Finset (Fin (Fintype.card B))) := by
    apply ((H.pullback eB).strong_image_iff H eB eB.injective
      (fun _ _ => Iff.rfl)
      ((Finset.univ : Finset (Fin (Fintype.card A))).image emb)
      (Finset.univ : Finset (Fin (Fintype.card B)))
      (Finset.subset_univ _)).mp
    rw [hEmbImage, Finset.image_univ_of_surjective eB.surjective]
    exact hStrong
  let d : StrongDiagram (Fintype.card A) (Fintype.card B) := {
    source := G.pullback eA
    target := H.pullback eB
    embedding := emb
    inj := hEmbInj
    induced := hInduced
    sparseSource := hSparseSource
    sparseTarget := hSparseTarget
    strong := hStrongNorm
  }
  refine ⟨eA, eB, d, ?_, ?_, ?_⟩
  · intro x y
    exact Iff.rfl
  · intro x y
    exact Iff.rfl
  · intro x
    change eB (eB.symm (f (eA x))) = f (eA x)
    exact eB.apply_symm_apply _

end FiniteCatalogue
end BigHrushovski
