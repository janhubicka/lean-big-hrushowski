import BigHrushovski.C0CoordinateFixedMatrixOrder

/-!
# One-stage selection for an actual finite ordered local C₀ representative

The finite-age converse supplies stage/value witnesses for the raw host.
The separate local order problem starts with a prescribed order on the
C-closed lower part of a one-generated finite diagram. We can select the
complete top matrix while fixing every lower position.

This file records the actual representative-to-matrix interface, rather
than postulating a hereditary catalogue. Its results refer to a SINGLE
given ordered local representative. They do not assert that choices for
different finite occurrences assemble into the countable host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {n : ℕ}

/-- A given finite ordered local representative admits a selected
complete top code that preserves the entire ordered lower subdiagram,
including nonedges and negative unary incidences. Every top vertex
still generates the complete local carrier. -/
theorem LocalOrderedRepresentative.selectedCompleteMatrix_oneStage
    (r : LocalOrderedRepresentative (Fin n)) :
    let M := r.completeMatrix
    M.selectedCode ∈ M.topOrbit ∧
    M.selectedCode.lowerPositions = M.lowerPositions ∧
    M.selectedCode.lowerCode = M.lowerCode ∧
    (∀ a : Fin n,
      (a ∈ M.lowerPositions →
        M.selectedCode.generatedSupport a = M.generatedSupport a ∧
        (∀ u ∈ M.generatedSupport a,
          ∀ v ∈ M.generatedSupport a,
            (u,v) ∈ M.selectedCode.adjacencyPairs ↔
              (u,v) ∈ M.adjacencyPairs) ∧
        (∀ u ∈ M.generatedSupport a,
          ∀ v ∈ M.generatedSupport a,
            (u,v) ∈ M.selectedCode.closurePairs ↔
              (u,v) ∈ M.closurePairs)) ∧
      (a ∉ M.lowerPositions →
        M.selectedCode.generatedSupport a = Finset.univ)) := by
  let M := r.completeMatrix
  have hClosed : M.LowerCClosed :=
    r.completeMatrix_lowerCClosed
  have hTop : M.AllTopGenerate :=
    r.completeMatrix_allTopGenerate
  refine ⟨M.selectedCode_mem_topOrbit, ?_, M.selectedCode_lowerCode, ?_⟩
  · obtain ⟨σ,hσ,hEq⟩ : ∃ σ : Equiv.Perm (Fin n),
        M.FixesLower σ ∧ M.relabel σ = M.selectedCode := by
      have hMem := M.selectedCode_mem_topOrbit
      classical
      obtain ⟨σ,hσ,hEq⟩ := Finset.mem_image.mp hMem
      exact ⟨σ,(Finset.mem_filter.mp hσ).2,hEq⟩
    rw [← hEq]
    exact M.relabel_lower_of_fixes σ hσ
  · intro a
    exact M.selectedCode_local_restrictions hClosed hTop a

/-- If two complete presentations differ only by re-enumerating the
top vertices over the *same ordered lower positions*, the selected
top code is literally identical. This is equality of COMPLETE codes,
not only equality of their positive graph edges. -/
theorem CompleteLocalMatrix.selectedCode_fixedLower_transport
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).selectedCode = M.selectedCode ∧
    (M.relabel σ).lowerCode = M.lowerCode := by
  exact ⟨M.selectedCode_relabel σ hσ,
    M.lowerCode_relabel σ hσ⟩

/-- Conversely, equality of selected full matrices identifies exactly
the same orbit of top re-enumerations fixing the ordered lower part.
It does not choose a physical labelling of a symmetric top component. -/
theorem CompleteLocalMatrix.selectedCode_eq_transport_iff
    (M N : CompleteLocalMatrix n) :
    M.selectedCode = N.selectedCode ↔
      ∃ σ : Equiv.Perm (Fin n),
        M.FixesLower σ ∧ M.relabel σ = N := by
  exact M.selectedCode_eq_iff N

end FiniteUnaryCoordinates
end BigHrushovski
