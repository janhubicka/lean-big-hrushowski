import BigHrushovski.GenericityCriterion

/-!
# The empty strong diagram is applicable at every two-sparse stage

The fair request schedule may present a request that is not applicable
at the current finite stage, or no request at all. To force strict
growth in every successor step without a second graph construction,
we use a fixed empty-to-empty strong diagram. It is applicable to
every two-sparse finite initial segment.

Once the growing Nat response theorem is available, answering this
trivial request provides a valid growth-only fallback. Nothing in
this module assumes or constructs an infinite chain.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The empty graph on Fin 0. -/
def emptyFinGraph : GraphOn (Fin 0) where
  adj _ _ := False
  symm := by
    intro x y h
    exact h
  irrefl := by
    intro x h
    exact h

theorem emptyFinGraph_sparse :
    emptyFinGraph.IsTwoSparse (Finset.univ : Finset (Fin 0)) := by
  classical
  have h : (Finset.univ : Finset (Fin 0)) = ∅ := by
    simp
  rw [h]
  exact emptyFinGraph.twoSparse_empty

/-- The empty inclusion is a finite strong embedding diagram. -/
def trivialStrongDiagram : StrongDiagram 0 0 where
  source := emptyFinGraph
  target := emptyFinGraph
  embedding := fun x => Fin.elim0 x
  inj := by
    intro x
    exact Fin.elim0 x
  induced := by
    intro x
    exact Fin.elim0 x
  sparseSource := emptyFinGraph_sparse
  sparseTarget := emptyFinGraph_sparse
  strong := by
    simpa using
      emptyFinGraph.toPredimension.strong_refl
        (Finset.univ : Finset (Fin 0))

/-- The empty strong diagram with the unique Nat-labelled source map. -/
def trivialRequest : ExtensionRequestCatalogue :=
  ⟨0, 0, (trivialStrongDiagram, fun x : Fin 0 => Fin.elim0 x)⟩

/-- The trivial request applies to every two-sparse finite stage.
Its source is empty and hence strong by two-sparsity. -/
theorem trivialRequest_applies
    (G : GraphOn ℕ) (n : ℕ)
    (hSparse : G.IsTwoSparse (Finset.range n)) :
    AppliesAt G (Finset.range n) trivialRequest := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact Fin.elim0 x
  · intro x
    exact Fin.elim0 x
  · change G.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin 0)).image
        (fun x : Fin 0 => (Fin.elim0 x : ℕ)))
      (Finset.range n)
    have hEmpty :
        ((Finset.univ : Finset (Fin 0)).image
          (fun x : Fin 0 => (Fin.elim0 x : ℕ))) = ∅ := by
      simp
    rw [hEmpty]
    exact G.empty_strong_of_twoSparse hSparse

end FiniteCatalogue
end BigHrushovski
