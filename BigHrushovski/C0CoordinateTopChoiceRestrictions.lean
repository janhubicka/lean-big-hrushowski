import BigHrushovski.C0CoordinateLocalTypeMatrixBridge

/-!
# Hereditary finite restrictions of a normalized local C₀ type

In the local-order induction the ordered lower part is fixed before
enumerating the new top component. Its complete C-values are closed
within the lower part, while every top vertex generates the entire
local structure.

The statements below separate these two cases. For a lower vertex,
the top normalization preserves its exact generated support and all
induced graph and C-incidences, including negative incidences. For a
top vertex, its complete C-value is the entire local carrier after
normalization.

This is an induction STEP over a given ordered lower part. It is not
yet a global construction of a coherent catalogue of finite local
types, nor a construction of the countable coordinate host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {n : ℕ}

/-- The full complete C-value of a vertex as a finite set of positions.
No arbitrary distinguished generator is used in the matrix itself. -/
noncomputable def CompleteLocalMatrix.generatedSupport
    (M : CompleteLocalMatrix n) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => (a,v) ∈ M.closurePairs)

@[simp] theorem CompleteLocalMatrix.mem_generatedSupport_iff
    (M : CompleteLocalMatrix n) (a v : Fin n) :
    v ∈ M.generatedSupport a ↔ (a,v) ∈ M.closurePairs := by
  classical
  simp [CompleteLocalMatrix.generatedSupport]

/-- The C-closure of each lower vertex remains entirely in the
already ordered lower part. The full-function closedness hypothesis
cannot be replaced by edge closure. -/
theorem CompleteLocalMatrix.generatedSupport_subset_lower
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed)
    (a : Fin n) (ha : a ∈ M.lowerPositions) :
    M.generatedSupport a ⊆ M.lowerPositions := by
  intro v hv
  exact hClosed a ha v ((M.mem_generatedSupport_iff a v).mp hv)

/-- Top normalization preserves the LITERAL full C-value of each
lower vertex, not merely its size or its isomorphism type. -/
theorem CompleteLocalMatrix.generatedSupport_normalForm
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed)
    (a : Fin n) (ha : a ∈ M.lowerPositions) :
    M.normalForm.generatedSupport a = M.generatedSupport a := by
  ext v
  exact (M.normalForm.mem_generatedSupport_iff a v).trans
    ((M.normalForm_lower_C_row hClosed a ha v).trans
      (M.mem_generatedSupport_iff a v).symm)

/-- Each complete graph entry (and each nonedge) between two lower
vertices survives the selected top normalization unchanged. -/
theorem CompleteLocalMatrix.normalForm_adj_on_lower
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n)
    (u v : Fin n)
    (hu : u ∈ M.lowerPositions) (hv : v ∈ M.lowerPositions) :
    (u,v) ∈ M.normalForm.adjacencyPairs ↔
      (u,v) ∈ M.adjacencyPairs := by
  obtain ⟨σ,hσ,hEq⟩ := M.normalForm_exists_permutation
  rw [← hEq]
  simpa only [hσ u hu, hσ v hv] using
    (M.mem_relabel_adjacency_iff σ u v)

/-- The complete C-entries inside any lower generated closure survive
top normalization, including absent incidences. -/
theorem CompleteLocalMatrix.normalForm_C_on_lower
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed)
    (u : Fin n) (hu : u ∈ M.lowerPositions)
    (v : Fin n) :
    (u,v) ∈ M.normalForm.closurePairs ↔
      (u,v) ∈ M.closurePairs :=
  M.normalForm_lower_C_row hClosed u hu v

/-- Exact hereditary restriction for each vertex of the already
ordered lower part. Its C-closure has the same literal support
and the same induced complete E/C matrices after normalizing the
top. The order on this fixed set of positions is inherited unchanged. -/
theorem CompleteLocalMatrix.normalForm_lower_generated_code
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed)
    (a : Fin n) (ha : a ∈ M.lowerPositions) :
    M.normalForm.generatedSupport a = M.generatedSupport a ∧
    (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
      (u,v) ∈ M.normalForm.adjacencyPairs ↔
        (u,v) ∈ M.adjacencyPairs) ∧
    (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
      (u,v) ∈ M.normalForm.closurePairs ↔
        (u,v) ∈ M.closurePairs) := by
  have hSub := M.generatedSupport_subset_lower hClosed a ha
  refine ⟨M.generatedSupport_normalForm hClosed a ha, ?_, ?_⟩
  · intro u hu v hv
    exact M.normalForm_adj_on_lower u v (hSub hu) (hSub hv)
  · intro u hu v _hv
    exact M.normalForm_C_on_lower hClosed u (hSub hu) v

/-- All top vertices generate the entire matrix carrier (a rootless
formulation: no top generator is distinguished). -/
def CompleteLocalMatrix.AllTopGenerate
    (M : CompleteLocalMatrix n) : Prop :=
  ∀ b : Fin n, b ∉ M.lowerPositions →
    ∀ v : Fin n, (b,v) ∈ M.closurePairs

/-- Every actual local representative has this rootless top
generation property for its complete matrix. -/
theorem LocalOrderedRepresentative.completeMatrix_allTopGenerate
    (r : LocalOrderedRepresentative (Fin n)) :
    r.completeMatrix.AllTopGenerate := by
  intro b hb v
  change b ∉ r.lower at hb
  have hVal := r.top_generates b hb
  exact (r.mem_completeMatrix_closure_iff b v).mpr (by
    rw [hVal]
    exact Finset.mem_univ v)

/-- The normalized top still consists precisely of generators of the
whole local diagram, even if several such vertices are symmetric. -/
theorem CompleteLocalMatrix.allTopGenerate_normalForm
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hTop : M.AllTopGenerate) :
    M.normalForm.AllTopGenerate := by
  obtain ⟨σ,hσ,hEq⟩ := M.normalForm_exists_permutation
  intro b hb v
  have hL : (M.relabel σ).lowerPositions = M.lowerPositions :=
    M.relabel_lower_of_fixes σ hσ
  have hb' : σ.symm b ∉ M.lowerPositions := by
    intro hm
    apply hb
    rw [← hEq, hL]
    simpa only [hσ _ hm, σ.apply_symm_apply] using hm
  have hc := hTop (σ.symm b) hb' (σ.symm v)
  rw [← hEq]
  have hRelabel := (M.mem_relabel_closure_iff σ (σ.symm b) (σ.symm v)).mpr hc
  simpa only [σ.apply_symm_apply] using hRelabel

/-- Finite orbit normalization is idempotent. The selected code is
itself the same selected type upon repeating the top-order choice. -/
theorem CompleteLocalMatrix.normalForm_idempotent
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) :
    M.normalForm.normalForm = M.normalForm := by
  exact ((M.normalForm).normalForm_eq_iff_orbit M.normalForm).mpr rfl

/-- The normalized matrix still has a lower part closed under all
complete unary values, not just under the induced lower matrix. -/
theorem CompleteLocalMatrix.lowerCClosed_normalForm
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed) :
    M.normalForm.LowerCClosed := by
  intro u hu v hC
  have hL : M.normalForm.lowerPositions = M.lowerPositions :=
    M.normalForm_lowerPositions
  rw [hL] at hu ⊢
  exact hClosed u hu v
    ((M.normalForm_lower_C_row hClosed u hu v).mp hC)

/-- The two cases needed for the hereditary induction: a lower
vertex retains its complete one-generated induced code, while every
top vertex generates all positions in the chosen normal form. -/
theorem CompleteLocalMatrix.normalForm_local_restrictions
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n)
    (hClosed : M.LowerCClosed) (hTop : M.AllTopGenerate)
    (a : Fin n) :
    (a ∈ M.lowerPositions →
      M.normalForm.generatedSupport a = M.generatedSupport a ∧
      (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
        (u,v) ∈ M.normalForm.adjacencyPairs ↔
          (u,v) ∈ M.adjacencyPairs) ∧
      (∀ u ∈ M.generatedSupport a, ∀ v ∈ M.generatedSupport a,
        (u,v) ∈ M.normalForm.closurePairs ↔
          (u,v) ∈ M.closurePairs)) ∧
    (a ∉ M.lowerPositions →
      M.normalForm.generatedSupport a = Finset.univ) := by
  constructor
  · intro ha
    exact M.normalForm_lower_generated_code hClosed a ha
  · intro ha
    apply Finset.eq_univ_of_forall
    intro v
    exact ((M.normalForm.mem_generatedSupport_iff a v).mpr
      (M.allTopGenerate_normalForm hTop a
        (by
          rw [M.normalForm_lowerPositions]
          exact ha) v))

end FiniteUnaryCoordinates
end BigHrushovski
