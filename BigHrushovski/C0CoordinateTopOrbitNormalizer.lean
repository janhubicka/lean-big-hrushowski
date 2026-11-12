import BigHrushovski.C0CoordinateTopPermutationOrbit

/-!
# Conditional canonical representative of a finite top-permutation orbit

Fix ONCE a total order on complete finite incidence matrices. The least
member of each top-permutation orbit is then well defined, belongs to
the original orbit, and is unchanged by relabelling which fixes the
ordered lower positions pointwise. Equality of least representatives
characterizes equality of complete top-permutation orbits.

The total order is an EXPLICIT parameter, rather than a physical order
on the vertices or an undocumented raw-name tie-break. These results
do not choose an order on an unordered lower closure, nor prove that
independently selected orders of lower closures are compatible across
different finite presentations. In particular, no global W is built.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {n : ℕ} [LinearOrder (CompleteLocalMatrix n)]

/-- The least COMPLETE matrix in the finite nonempty orbit. The total
ordering of matrix codes is a supplied common comparison convention,
not an ordering of original vertex names. -/
noncomputable def CompleteLocalMatrix.normalForm
    (M : CompleteLocalMatrix n) : CompleteLocalMatrix n :=
  M.topOrbit.min' ⟨M, M.mem_topOrbit_self⟩

/-- The selected code is realized by a top permutation of the input. -/
theorem CompleteLocalMatrix.normalForm_mem
    (M : CompleteLocalMatrix n) :
    M.normalForm ∈ M.topOrbit := by
  unfold CompleteLocalMatrix.normalForm
  exact Finset.min'_mem M.topOrbit ⟨M, M.mem_topOrbit_self⟩

/-- An orbit member has exactly the same orbit as its source. The
complete C and adjacency matrices, including negative incidences,
are transported together. -/
theorem CompleteLocalMatrix.topOrbit_eq_of_mem
    (M N : CompleteLocalMatrix n) (hN : N ∈ M.topOrbit) :
    M.topOrbit = N.topOrbit := by
  classical
  obtain ⟨σ, hσ, hEq⟩ := Finset.mem_image.mp hN
  have hFix : M.FixesLower σ := (Finset.mem_filter.mp hσ).2
  rw [← hEq]
  exact (M.topOrbit_relabel σ hFix).symm

/-- Two normalized complete matrices agree exactly when the original
top-permutation orbits agree; no named generator is involved. -/
theorem CompleteLocalMatrix.normalForm_eq_iff_orbit
    (M N : CompleteLocalMatrix n) :
    M.normalForm = N.normalForm ↔ M.topOrbit = N.topOrbit := by
  constructor
  · intro h
    calc
      M.topOrbit = M.normalForm.topOrbit :=
        M.topOrbit_eq_of_mem M.normalForm M.normalForm_mem
      _ = N.normalForm.topOrbit := by rw [h]
      _ = N.topOrbit :=
        (N.topOrbit_eq_of_mem N.normalForm N.normalForm_mem).symm
  · intro h
    unfold CompleteLocalMatrix.normalForm
    apply le_antisymm
    · apply Finset.min'_le
      rw [h]
      exact Finset.min'_mem _ _
    · apply Finset.min'_le
      rw [← h]
      exact Finset.min'_mem _ _

/-- Changing only the top coordinates does not alter the selected
complete normal form relative to the SAME ordered lower positions. -/
theorem CompleteLocalMatrix.normalForm_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).normalForm = M.normalForm := by
  exact ((M.relabel σ).normalForm_eq_iff_orbit M).mpr
    (M.topOrbit_relabel σ hσ)

/-- Equality of normalized codes is EXACTLY a complete top relabelling
fixing each ordered lower position, not merely an edge-homomorphism. -/
theorem CompleteLocalMatrix.normalForm_eq_iff_topPerm
    (M N : CompleteLocalMatrix n) :
    M.normalForm = N.normalForm ↔
      ∃ σ : Equiv.Perm (Fin n),
        M.FixesLower σ ∧ M.relabel σ = N := by
  exact (M.normalForm_eq_iff_orbit N).trans
    (M.topOrbit_eq_iff N)

/-- Every selected normal form is attained by an actual finite
permutation of the top, fixing the lower positions pointwise. -/
theorem CompleteLocalMatrix.normalForm_exists_permutation
    (M : CompleteLocalMatrix n) :
    ∃ σ : Equiv.Perm (Fin n),
      M.FixesLower σ ∧ M.relabel σ = M.normalForm := by
  classical
  obtain ⟨σ, hσ, hEq⟩ := Finset.mem_image.mp M.normalForm_mem
  exact ⟨σ, (Finset.mem_filter.mp hσ).2, hEq⟩

end FiniteUnaryCoordinates
end BigHrushovski
