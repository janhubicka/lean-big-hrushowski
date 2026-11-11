import BigHrushovski.C0CoordinateLocalOccurrenceFamily

/-!
# Finite top-permutation orbits of complete local C₀ matrices

A chosen order on the lower closure is part of a local type. To choose
an internal order on the top component, consider all complete graph
and unary-value matrices obtained by permuting only the top positions.

The lower positions are fixed POINTWISE. The resulting orbit is a
finite nonempty set, invariant under any such permutation. Equality of
these orbits is equivalent to the existence of a top permutation
carrying one complete matrix to the other. Thus an orbit, rather than
an arbitrary labelled graph or a chosen generator, is the correct
finite key for selecting a uniform local ordered isomorphism type.

This is finite normal-form infrastructure. The identification of
these orbits with ALL permitted local C₀ types over already ordered
lower parts, and the recursive hereditary selection, remain separate.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The complete finite edge and unary-incidence matrices, with the
positions occupied by an ALREADY ORDERED lower closure distinguished.
There is no pointed generator in this record. -/
structure CompleteLocalMatrix (n : ℕ) where
  adjacencyPairs : Finset (Fin n × Fin n)
  closurePairs : Finset (Fin n × Fin n)
  lowerPositions : Finset (Fin n)
deriving DecidableEq

/-- Permute both entries of every matrix pair. -/
def localPermutePair {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Fin n × Fin n) : Fin n × Fin n :=
  (σ p.1, σ p.2)

/-- Relabel all COMPLETE graph and unary matrices by a permutation. -/
noncomputable def CompleteLocalMatrix.relabel {n : ℕ}
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n)) :
    CompleteLocalMatrix n where
  adjacencyPairs := M.adjacencyPairs.image (localPermutePair σ)
  closurePairs := M.closurePairs.image (localPermutePair σ)
  lowerPositions := M.lowerPositions.image σ

@[simp] theorem CompleteLocalMatrix.relabel_refl {n : ℕ}
    (M : CompleteLocalMatrix n) :
    M.relabel (Equiv.refl (Fin n)) = M := by
  classical
  have hId : localPermutePair (Equiv.refl (Fin n)) = id := by
    funext p
    rcases p with ⟨u, v⟩
    rfl
  cases M
  simp [CompleteLocalMatrix.relabel, hId]

/-- Relabellings compose exactly; the coordinate-map action requires
no isomorphism quotient or distinguished root. -/
theorem CompleteLocalMatrix.relabel_trans {n : ℕ}
    (M : CompleteLocalMatrix n)
    (σ τ : Equiv.Perm (Fin n)) :
    (M.relabel σ).relabel τ = M.relabel (σ.trans τ) := by
  classical
  have hComp : localPermutePair (σ.trans τ) =
      (localPermutePair τ) ∘ (localPermutePair σ) := by
    funext p
    rcases p with ⟨u, v⟩
    rfl
  cases M
  simp [CompleteLocalMatrix.relabel, Finset.image_image,
    hComp, Function.comp_def, Equiv.trans_apply]

/-- A top permutation fixes every vertex of the ordered lower
closure, not merely the lower set as an unordered subset. -/
def CompleteLocalMatrix.FixesLower {n : ℕ}
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ u ∈ M.lowerPositions, σ u = u

theorem CompleteLocalMatrix.fixesLower_refl {n : ℕ}
    (M : CompleteLocalMatrix n) :
    M.FixesLower (Equiv.refl (Fin n)) :=
  fun _ _ => rfl

theorem CompleteLocalMatrix.fixesLower_trans {n : ℕ}
    (M : CompleteLocalMatrix n) (σ τ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) (hτ : M.FixesLower τ) :
    M.FixesLower (σ.trans τ) := by
  intro u hu
  change τ (σ u) = u
  rw [hσ u hu, hτ u hu]

theorem CompleteLocalMatrix.fixesLower_symm {n : ℕ}
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    M.FixesLower σ.symm := by
  intro u hu
  calc
    σ.symm u = σ.symm (σ u) := by rw [hσ u hu]
    _ = u := σ.symm_apply_apply u

theorem CompleteLocalMatrix.relabel_lower_of_fixes {n : ℕ}
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).lowerPositions = M.lowerPositions := by
  classical
  change M.lowerPositions.image σ = M.lowerPositions
  ext u
  constructor
  · intro hu
    obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
    have heq : v = u := (hσ v hv).symm.trans hvu
    simpa only [heq] using hv
  · intro hu
    exact Finset.mem_image.mpr ⟨u,hu,hσ u hu⟩

/-- Every top-permutation orbit is a FINITE set of complete codes. -/
noncomputable def CompleteLocalMatrix.topOrbit {n : ℕ}
    (M : CompleteLocalMatrix n) : Finset (CompleteLocalMatrix n) := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    M.FixesLower σ)).image M.relabel

/-- The orbit contains its original complete matrix, using the
identity permutation fixing the ordered lower part. -/
theorem CompleteLocalMatrix.mem_topOrbit_self {n : ℕ}
    (M : CompleteLocalMatrix n) : M ∈ M.topOrbit := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨Equiv.refl (Fin n), ?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, M.fixesLower_refl⟩
  · exact M.relabel_refl

/-- Top permutation does not change the COMPLETE orbit. This is the
basic presentation-independent code used by finite local types. -/
theorem CompleteLocalMatrix.topOrbit_relabel {n : ℕ}
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).topOrbit = M.topOrbit := by
  classical
  have hLower : (M.relabel σ).lowerPositions =
      M.lowerPositions := M.relabel_lower_of_fixes σ hσ
  ext X
  constructor
  · intro hX
    obtain ⟨τ,hτ,hEq⟩ := Finset.mem_image.mp hX
    have hFixτ : M.FixesLower τ := by
      have h := (Finset.mem_filter.mp hτ).2
      simpa only [CompleteLocalMatrix.FixesLower, hLower] using h
    apply Finset.mem_image.mpr
    refine ⟨σ.trans τ, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, M.fixesLower_trans σ τ hσ hFixτ⟩
    · exact (M.relabel_trans σ τ).symm.trans hEq
  · intro hX
    obtain ⟨ρ,hρ,hEq⟩ := Finset.mem_image.mp hX
    have hFixρ : M.FixesLower ρ := (Finset.mem_filter.mp hρ).2
    let τ : Equiv.Perm (Fin n) := σ.symm.trans ρ
    have hFixτ : (M.relabel σ).FixesLower τ := by
      change ∀ u ∈ (M.relabel σ).lowerPositions, τ u = u
      rw [hLower]
      exact M.fixesLower_trans σ.symm ρ
        (M.fixesLower_symm σ hσ) hFixρ
    apply Finset.mem_image.mpr
    refine ⟨τ, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hFixτ⟩, ?_⟩
    have hCancel : σ.trans τ = ρ := by
      ext x
      simp [τ]
    rw [M.relabel_trans σ τ, hCancel]
    exact hEq

/-- Two complete local matrices have the SAME orbit exactly when
they differ by a permutation fixing every ordered lower position.
This is a finite normal-form completeness theorem, without naming
an arbitrary top vertex or imposing automorphism rigidity. -/
theorem CompleteLocalMatrix.topOrbit_eq_iff {n : ℕ}
    (M N : CompleteLocalMatrix n) :
    M.topOrbit = N.topOrbit ↔
      ∃ σ : Equiv.Perm (Fin n),
        M.FixesLower σ ∧ M.relabel σ = N := by
  classical
  constructor
  · intro h
    have hN : N ∈ M.topOrbit := by
      rw [h]
      exact N.mem_topOrbit_self
    obtain ⟨σ,hσ,hEq⟩ := Finset.mem_image.mp hN
    exact ⟨σ,(Finset.mem_filter.mp hσ).2,hEq⟩
  · rintro ⟨σ,hσ,hEq⟩
    rw [← hEq]
    exact (M.topOrbit_relabel σ hσ).symm

end FiniteUnaryCoordinates
end BigHrushovski
