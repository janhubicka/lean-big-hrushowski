import BigHrushovski.C0CoordinateTopChoiceRestrictions

/-!
# A single total order on complete local matrix codes of each finite size

The finite top-orbit normalizer is parametric in a linear order on
`CompleteLocalMatrix n`. This file removes that parameter by choosing
one such order ONCE for each n. A complete local matrix is a tuple
of three finite subsets of finite sets, hence there are only finitely
many matrices of each fixed size.

The chosen total order need not be lexicographic; choosing any one
order on the *complete code space* has the same mathematical effect.
It is fixed for all occurrences of that finite code size, rather than
chosen from raw labels of the source structure.

This is a uniform finite selector relative to an already ordered
lower part. It does NOT yet show which normalized codes correspond to
the complete admissible finite C₀ age or construct a hereditary global
catalogue of admissible local types.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {n : ℕ}

/-- Once-and-for-all linear order on all complete n-position codes.
The finiteness proof forgets no information: the three full
incidence fields give an injective encoding into a finite product. -/
noncomputable def CompleteLocalMatrix.fixedOrder (n : ℕ) :
    LinearOrder (CompleteLocalMatrix n) := by
  classical
  let f : CompleteLocalMatrix n →
      (Finset (Fin n × Fin n) ×
        (Finset (Fin n × Fin n) × Finset (Fin n))) :=
    fun M => (M.adjacencyPairs, (M.closurePairs, M.lowerPositions))
  have hf : Function.Injective f := by
    intro M N h
    apply CompleteLocalMatrix.ext
    · exact congrArg Prod.fst h
    · exact congrArg (fun t => t.2.1) h
    · exact congrArg (fun t => t.2.2) h
  letI : Finite (CompleteLocalMatrix n) := Finite.of_injective f hf
  letI : Fintype (CompleteLocalMatrix n) := Fintype.ofFinite _
  let e := Fintype.equivFin (CompleteLocalMatrix n)
  exact LinearOrder.lift' e e.injective

/-- The selected complete code, with no local typeclass parameter or
choice depending on raw vertex labels. The lower positions are part
of the input code and must already be ordered. -/
noncomputable def CompleteLocalMatrix.selectedCode
    (M : CompleteLocalMatrix n) : CompleteLocalMatrix n :=
  @CompleteLocalMatrix.normalForm n (CompleteLocalMatrix.fixedOrder n) M

/-- The once-and-for-all choice is attained by a top permutation
fixing every already ordered lower position pointwise. -/
theorem CompleteLocalMatrix.selectedCode_mem_topOrbit
    (M : CompleteLocalMatrix n) :
    M.selectedCode ∈ M.topOrbit := by
  exact @CompleteLocalMatrix.normalForm_mem n
    (CompleteLocalMatrix.fixedOrder n) M

/-- The chosen finite code is presentation-independent under all
top permutations fixing the ordered lower positions pointwise. -/
theorem CompleteLocalMatrix.selectedCode_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).selectedCode = M.selectedCode := by
  exact @CompleteLocalMatrix.normalForm_relabel n
    (CompleteLocalMatrix.fixedOrder n) M σ hσ

/-- Equal selected complete codes characterize the exact
top-permutation orbit, including graph nonedges and all C-values. -/
theorem CompleteLocalMatrix.selectedCode_eq_iff
    (M N : CompleteLocalMatrix n) :
    M.selectedCode = N.selectedCode ↔
      ∃ σ : Equiv.Perm (Fin n),
        M.FixesLower σ ∧ M.relabel σ = N := by
  exact @CompleteLocalMatrix.normalForm_eq_iff_topPerm n
    (CompleteLocalMatrix.fixedOrder n) M N

/-- The selected code agrees literally with the original complete
graph/C matrix on the ordered lower part. -/
theorem CompleteLocalMatrix.selectedCode_lowerCode
    (M : CompleteLocalMatrix n) :
    M.selectedCode.lowerCode = M.lowerCode := by
  exact @CompleteLocalMatrix.normalForm_lowerCode n
    (CompleteLocalMatrix.fixedOrder n) M

/-- All lower one-generated restrictions are preserved, and every
top vertex remains a full generator, for the actual fixed-order
selection, without any order parameter in the statement. -/
theorem CompleteLocalMatrix.selectedCode_local_restrictions
    (M : CompleteLocalMatrix n)
    (hClosed : M.LowerCClosed) (hTop : M.AllTopGenerate)
    (a : Fin n) :
    (a ∈ M.lowerPositions →
      M.selectedCode.generatedSupport a = M.generatedSupport a ∧
      (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
        (u,v) ∈ M.selectedCode.adjacencyPairs ↔
          (u,v) ∈ M.adjacencyPairs) ∧
      (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
        (u,v) ∈ M.selectedCode.closurePairs ↔
          (u,v) ∈ M.closurePairs)) ∧
    (a ∉ M.lowerPositions →
      M.selectedCode.generatedSupport a = Finset.univ) := by
  exact @CompleteLocalMatrix.normalForm_local_restrictions n
    (CompleteLocalMatrix.fixedOrder n) M hClosed hTop a

/-- Applying the finite selection twice has no effect. -/
theorem CompleteLocalMatrix.selectedCode_idempotent
    (M : CompleteLocalMatrix n) :
    M.selectedCode.selectedCode = M.selectedCode := by
  exact @CompleteLocalMatrix.normalForm_idempotent n
    (CompleteLocalMatrix.fixedOrder n) M

end FiniteUnaryCoordinates
end BigHrushovski
