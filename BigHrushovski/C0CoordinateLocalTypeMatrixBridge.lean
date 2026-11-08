import BigHrushovski.C0CoordinateTopOrbitNormalizer

/-!
# Complete finite local-type matrices from actual ordered representatives

This file connects the combinatorial orbit record to the finite rootless
local representatives used in the C0 ordered age. The complete adjacency
and unary-incidence matrices include nonedges and every member of C(u).

The matrix records the INDUCED ORDER by positions; a top permutation
re-enumerates positions without being an automorphism of the selected
ordered representative. The original lower positions stay fixed.
This is a finite bridge only. Uniform chosen-type coverage and W remain open.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {n : ℕ}

/-- Reify an actual chosen local representative as its complete ordered
graph/unary incidence matrices, with the intrinsic lower positions. -/
noncomputable def LocalOrderedRepresentative.completeMatrix
    (r : LocalOrderedRepresentative (Fin n)) : CompleteLocalMatrix n where
  adjacencyPairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => r.graph.adj p.1 p.2)
  closurePairs := (Finset.univ.product Finset.univ).filter
    (fun p : Fin n × Fin n => p.2 ∈ r.value p.1)
  lowerPositions := r.lower

/-- Graph incidence is equivalent in both directions; absence of a
matrix pair records precisely a nonedge. -/
theorem LocalOrderedRepresentative.mem_completeMatrix_adj_iff
    (r : LocalOrderedRepresentative (Fin n)) (u v : Fin n) :
    (u,v) ∈ r.completeMatrix.adjacencyPairs ↔ r.graph.adj u v := by
  classical
  simp [LocalOrderedRepresentative.completeMatrix]

/-- The whole named unary C-value is reified, not merely cardinality. -/
theorem LocalOrderedRepresentative.mem_completeMatrix_closure_iff
    (r : LocalOrderedRepresentative (Fin n)) (u v : Fin n) :
    (u,v) ∈ r.completeMatrix.closurePairs ↔ v ∈ r.value u := by
  classical
  simp [LocalOrderedRepresentative.completeMatrix]

/-- The order of the lower closure is an initial segment of the
finite representative, because all top vertices follow all lower ones. -/
theorem LocalOrderedRepresentative.lower_downward_closed
    (r : LocalOrderedRepresentative (Fin n)) (u v : Fin n)
    (hu : u ∈ r.lower) (hvu : v < u) : v ∈ r.lower := by
  by_contra hv
  have huv : u < v := r.lower_before_top u hu v hv
  exact (lt_asymm huv hvu)

/-- Re-enumeration of the complete graph matrix transports both edges
and nonedges exactly. -/
theorem CompleteLocalMatrix.mem_relabel_adjacency_iff
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (u v : Fin n) :
    (σ u,σ v) ∈ (M.relabel σ).adjacencyPairs ↔
      (u,v) ∈ M.adjacencyPairs := by
  classical
  change (σ u,σ v) ∈ M.adjacencyPairs.image (localPermutePair σ) ↔ _
  constructor
  · intro h
    obtain ⟨⟨x,y⟩, hxy, hEq⟩ := Finset.mem_image.mp h
    have hx : x = u := σ.injective (congrArg Prod.fst hEq)
    have hy : y = v := σ.injective (congrArg Prod.snd hEq)
    simpa only [hx,hy] using hxy
  · intro h
    exact Finset.mem_image.mpr ⟨(u,v),h,rfl⟩

/-- The same re-enumeration reflects every entry of the COMPLETE
set-valued unary matrix. -/
theorem CompleteLocalMatrix.mem_relabel_closure_iff
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (u v : Fin n) :
    (σ u,σ v) ∈ (M.relabel σ).closurePairs ↔
      (u,v) ∈ M.closurePairs := by
  classical
  change (σ u,σ v) ∈ M.closurePairs.image (localPermutePair σ) ↔ _
  constructor
  · intro h
    obtain ⟨⟨x,y⟩, hxy, hEq⟩ := Finset.mem_image.mp h
    have hx : x = u := σ.injective (congrArg Prod.fst hEq)
    have hy : y = v := σ.injective (congrArg Prod.snd hEq)
    simpa only [hx,hy] using hxy
  · intro h
    exact Finset.mem_image.mpr ⟨(u,v),h,rfl⟩

/-- A relabelled lower member is exactly the same underlying lower
position before relabelling. -/
theorem CompleteLocalMatrix.mem_relabel_lower_iff
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (u : Fin n) :
    σ u ∈ (M.relabel σ).lowerPositions ↔
      u ∈ M.lowerPositions := by
  classical
  change σ u ∈ M.lowerPositions.image σ ↔ _
  constructor
  · intro h
    obtain ⟨v,hv,hEq⟩ := Finset.mem_image.mp h
    have hvu : v = u := σ.injective hEq
    simpa only [hvu] using hv
  · intro h
    exact Finset.mem_image.mpr ⟨u,h,rfl⟩

/-- Equality of complete re-enumerated matrices forces an exact
graph/unary/lower correspondence. In particular no nonedge or complete
C-value member can disappear in the comparison. -/
theorem LocalOrderedRepresentative.completeMatrix_eq_reflects
    (r s : LocalOrderedRepresentative (Fin n))
    (σ : Equiv.Perm (Fin n))
    (h : r.completeMatrix.relabel σ = s.completeMatrix) :
    (∀ u v : Fin n,
      r.graph.adj u v ↔ s.graph.adj (σ u) (σ v)) ∧
    (∀ u v : Fin n,
      v ∈ r.value u ↔ σ v ∈ s.value (σ u)) ∧
    (∀ u : Fin n, u ∈ r.lower ↔ σ u ∈ s.lower) := by
  have hA := congrArg CompleteLocalMatrix.adjacencyPairs h
  have hC := congrArg CompleteLocalMatrix.closurePairs h
  have hL := congrArg CompleteLocalMatrix.lowerPositions h
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [← r.mem_completeMatrix_adj_iff u v,
      ← (r.completeMatrix.mem_relabel_adjacency_iff σ u v),
      hA, s.mem_completeMatrix_adj_iff]
  · intro u v
    rw [← r.mem_completeMatrix_closure_iff u v,
      ← (r.completeMatrix.mem_relabel_closure_iff σ u v),
      hC, s.mem_completeMatrix_closure_iff]
  · intro u
    rw [← (r.completeMatrix.mem_relabel_lower_iff σ u),
      hL]
    rfl

end FiniteUnaryCoordinates
end BigHrushovski
