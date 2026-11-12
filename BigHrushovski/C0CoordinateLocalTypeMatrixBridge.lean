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
    (r : LocalOrderedRepresentative (Fin n)) : CompleteLocalMatrix n := by
  classical
  exact {
    adjacencyPairs := (Finset.univ.product Finset.univ).filter
      (fun p : Fin n × Fin n => r.graph.adj p.1 p.2)
    closurePairs := (Finset.univ.product Finset.univ).filter
      (fun p : Fin n × Fin n => p.2 ∈ r.value p.1)
    lowerPositions := r.lower
  }

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
    change u ∈ r.completeMatrix.lowerPositions ↔
      σ u ∈ s.completeMatrix.lowerPositions
    rw [← (r.completeMatrix.mem_relabel_lower_iff σ u), hL]


/-- Extensionality of complete local matrix records. -/
theorem CompleteLocalMatrix.ext
    {M N : CompleteLocalMatrix n}
    (hA : M.adjacencyPairs = N.adjacencyPairs)
    (hC : M.closurePairs = N.closurePairs)
    (hL : M.lowerPositions = N.lowerPositions) : M = N := by
  cases M
  cases N
  cases hA
  cases hC
  cases hL
  rfl

/-- The converse to reflection: all graph pairs, all complete C-value
memberships, and the exact lower positions determine the whole reified
matrix. Thus top-orbit equivalence on actual local representatives is
exactly complete unpointed isomorphism over their ordered lower parts. -/
theorem LocalOrderedRepresentative.completeMatrix_relabel_iff
    (r s : LocalOrderedRepresentative (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    r.completeMatrix.relabel σ = s.completeMatrix ↔
      (∀ u v : Fin n,
        r.graph.adj u v ↔ s.graph.adj (σ u) (σ v)) ∧
      (∀ u v : Fin n,
        v ∈ r.value u ↔ σ v ∈ s.value (σ u)) ∧
      (∀ u : Fin n, u ∈ r.lower ↔ σ u ∈ s.lower) := by
  constructor
  · exact r.completeMatrix_eq_reflects s σ
  · rintro ⟨hAdj, hC, hLower⟩
    apply CompleteLocalMatrix.ext
    · ext p
      rcases p with ⟨x,y⟩
      have hAdj' :
          r.graph.adj (σ.symm x) (σ.symm y) ↔
            s.graph.adj x y := by
        simpa only [σ.apply_symm_apply] using
          hAdj (σ.symm x) (σ.symm y)
      have hFull :=
        (r.completeMatrix.mem_relabel_adjacency_iff
          σ (σ.symm x) (σ.symm y)).trans
          ((r.mem_completeMatrix_adj_iff (σ.symm x)
              (σ.symm y)).trans
            (hAdj'.trans
              (s.mem_completeMatrix_adj_iff x y).symm))
      simpa only [σ.apply_symm_apply] using hFull
    · ext p
      rcases p with ⟨x,y⟩
      have hC' :
          (σ.symm y) ∈ r.value (σ.symm x) ↔
            y ∈ s.value x := by
        simpa only [σ.apply_symm_apply] using
          hC (σ.symm x) (σ.symm y)
      have hFull :=
        (r.completeMatrix.mem_relabel_closure_iff
          σ (σ.symm x) (σ.symm y)).trans
          ((r.mem_completeMatrix_closure_iff
              (σ.symm x) (σ.symm y)).trans
            (hC'.trans
              (s.mem_completeMatrix_closure_iff x y).symm))
      simpa only [σ.apply_symm_apply] using hFull
    · ext x
      have hFull :=
        (r.completeMatrix.mem_relabel_lower_iff
          σ (σ.symm x)).trans (hLower (σ.symm x))
      simpa only [σ.apply_symm_apply,
        LocalOrderedRepresentative.completeMatrix] using hFull

/-- Equality of complete top-permutation orbits of ACTUAL local
representatives is exactly a full unpointed graph/unary isomorphism
fixing the lower positions. The order on the lower positions is supplied
and held fixed; this does not select compatible lower orders globally. -/
theorem LocalOrderedRepresentative.completeMatrix_orbit_eq_iff
    (r s : LocalOrderedRepresentative (Fin n)) :
    r.completeMatrix.topOrbit = s.completeMatrix.topOrbit ↔
      ∃ σ : Equiv.Perm (Fin n),
        (∀ u ∈ r.lower, σ u = u) ∧
        (∀ u v : Fin n,
          r.graph.adj u v ↔ s.graph.adj (σ u) (σ v)) ∧
        (∀ u v : Fin n,
          v ∈ r.value u ↔ σ v ∈ s.value (σ u)) ∧
        (∀ u : Fin n, u ∈ r.lower ↔ σ u ∈ s.lower) := by
  rw [r.completeMatrix.topOrbit_eq_iff s.completeMatrix]
  constructor
  · rintro ⟨σ,hFix,hEq⟩
    obtain ⟨hAdj,hC,hLower⟩ :=
      r.completeMatrix_eq_reflects s σ hEq
    exact ⟨σ,hFix,hAdj,hC,hLower⟩
  · rintro ⟨σ,hFix,hAdj,hC,hLower⟩
    exact ⟨σ,hFix,(r.completeMatrix_relabel_iff s σ).mpr
      ⟨hAdj,hC,hLower⟩⟩


/-!
## The selected top order does not alter the ordered lower code

The lower part is already ordered when the next top component is
normalized. Its complete induced graph and C-incidence matrices must
remain LITERALLY fixed. This is stronger than an assertion about
isomorphism types, and includes nonedges and negative C-incidences.
-/

/-- All adjacency entries with BOTH coordinates in the already ordered
lower closure. This is a literal restriction, not a quotient. -/
noncomputable def CompleteLocalMatrix.lowerAdjacencyPairs
    (M : CompleteLocalMatrix n) : Finset (Fin n × Fin n) :=
  M.adjacencyPairs.filter
    (fun p => p.1 ∈ M.lowerPositions ∧ p.2 ∈ M.lowerPositions)

/-- All C-incidences with BOTH coordinates in the ordered lower part. -/
noncomputable def CompleteLocalMatrix.lowerClosurePairs
    (M : CompleteLocalMatrix n) : Finset (Fin n × Fin n) :=
  M.closurePairs.filter
    (fun p => p.1 ∈ M.lowerPositions ∧ p.2 ∈ M.lowerPositions)

/-- The exact complete graph/C code induced on the ordered lower part. -/
noncomputable def CompleteLocalMatrix.lowerCode
    (M : CompleteLocalMatrix n) :
    Finset (Fin n × Fin n) × Finset (Fin n × Fin n) :=
  (M.lowerAdjacencyPairs, M.lowerClosurePairs)

/-- Reordering only the top cannot alter a single adjacency entry
among the already ordered lower positions, including nonedges. -/
theorem CompleteLocalMatrix.lowerAdjacencyPairs_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).lowerAdjacencyPairs = M.lowerAdjacencyPairs := by
  classical
  have hL : (M.relabel σ).lowerPositions = M.lowerPositions :=
    M.relabel_lower_of_fixes σ hσ
  ext p
  rcases p with ⟨u,v⟩
  by_cases hu : u ∈ M.lowerPositions
  · by_cases hv : v ∈ M.lowerPositions
    · have hAdj : (u,v) ∈ (M.relabel σ).adjacencyPairs ↔
          (u,v) ∈ M.adjacencyPairs := by
        simpa only [hσ u hu, hσ v hv] using
          M.mem_relabel_adjacency_iff σ u v
      simpa [CompleteLocalMatrix.lowerAdjacencyPairs, hL, hu, hv] using hAdj
    · simp [CompleteLocalMatrix.lowerAdjacencyPairs, hL, hv]
  · simp [CompleteLocalMatrix.lowerAdjacencyPairs, hL, hu]

/-- A top permutation likewise fixes every complete unary C-incidence
whose source and target both lie in the ordered lower part. -/
theorem CompleteLocalMatrix.lowerClosurePairs_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).lowerClosurePairs = M.lowerClosurePairs := by
  classical
  have hL : (M.relabel σ).lowerPositions = M.lowerPositions :=
    M.relabel_lower_of_fixes σ hσ
  ext p
  rcases p with ⟨u,v⟩
  by_cases hu : u ∈ M.lowerPositions
  · by_cases hv : v ∈ M.lowerPositions
    · have hC : (u,v) ∈ (M.relabel σ).closurePairs ↔
          (u,v) ∈ M.closurePairs := by
        simpa only [hσ u hu, hσ v hv] using
          M.mem_relabel_closure_iff σ u v
      simpa [CompleteLocalMatrix.lowerClosurePairs, hL, hu, hv] using hC
    · simp [CompleteLocalMatrix.lowerClosurePairs, hL, hv]
  · simp [CompleteLocalMatrix.lowerClosurePairs, hL, hu]

/-- The complete lower code is fixed by EVERY allowed top permutation,
without choosing a root or comparing only positive graph edges. -/
theorem CompleteLocalMatrix.lowerCode_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) :
    (M.relabel σ).lowerCode = M.lowerCode := by
  exact Prod.ext
    (M.lowerAdjacencyPairs_relabel σ hσ)
    (M.lowerClosurePairs_relabel σ hσ)

/-- The orbit normalizer retains each position of the already ordered
lower part, not merely the cardinality of that part. -/
theorem CompleteLocalMatrix.normalForm_lowerPositions
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) :
    M.normalForm.lowerPositions = M.lowerPositions := by
  obtain ⟨σ,hσ,hEq⟩ := M.normalForm_exists_permutation
  rw [← hEq]
  exact M.relabel_lower_of_fixes σ hσ

/-- The complete induced lower code is independent of every possible
choice of a minimum-achieving enumeration of the top component.
This is the FINITE compatibility step used by recursive local choice;
it does not by itself produce a global hereditary catalogue. -/
theorem CompleteLocalMatrix.normalForm_lowerCode
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) :
    M.normalForm.lowerCode = M.lowerCode := by
  obtain ⟨σ,hσ,hEq⟩ := M.normalForm_exists_permutation
  rw [← hEq]
  exact M.lowerCode_relabel σ hσ


/-!
## Closed lower parts: preservation of full unary rows

The lower × lower code already suffices for an actual local
representative because its lower part is C-closed. In this case no
value C(u), for u lower, can contain an element of the top. We record
the stronger row statement explicitly, rather than tacitly inferring
it for arbitrary binary matrices.
-/

/-- The distinguished ordered lower positions are closed under the
COMPLETE named C-values. This does not hold for an arbitrary code. -/
def CompleteLocalMatrix.LowerCClosed
    (M : CompleteLocalMatrix n) : Prop :=
  ∀ u ∈ M.lowerPositions, ∀ v : Fin n,
    (u,v) ∈ M.closurePairs → v ∈ M.lowerPositions

/-- Actual finite ordered local representatives satisfy the full
C-closedness hypothesis needed to freeze all lower source rows. -/
theorem LocalOrderedRepresentative.completeMatrix_lowerCClosed
    (r : LocalOrderedRepresentative (Fin n)) :
    r.completeMatrix.LowerCClosed := by
  intro u hu v hC
  change u ∈ r.lower at hu
  have hC' : v ∈ r.value u :=
    (r.mem_completeMatrix_closure_iff u v).mp hC
  exact r.lower_closed u hu hC'

/-- A top permutation preserves the ENTIRE C-row from each ordered
lower vertex, including every negative entry towards the top, when
the lower part is closed under the complete function values. -/
theorem CompleteLocalMatrix.closed_lower_C_row_relabel
    (M : CompleteLocalMatrix n) (σ : Equiv.Perm (Fin n))
    (hσ : M.FixesLower σ) (hClosed : M.LowerCClosed)
    (u : Fin n) (hu : u ∈ M.lowerPositions) (v : Fin n) :
    (u,v) ∈ (M.relabel σ).closurePairs ↔
      (u,v) ∈ M.closurePairs := by
  have hShift : (u,v) ∈ (M.relabel σ).closurePairs ↔
      (u,σ.symm v) ∈ M.closurePairs := by
    simpa only [hσ u hu, σ.apply_symm_apply] using
      (M.mem_relabel_closure_iff σ u (σ.symm v))
  apply hShift.trans
  constructor
  · intro h
    have hv : σ.symm v ∈ M.lowerPositions :=
      hClosed u hu (σ.symm v) h
    have hvEq : σ.symm v = v := by
      calc
        σ.symm v = σ (σ.symm v) := (hσ _ hv).symm
        _ = v := σ.apply_symm_apply v
    simpa only [hvEq] using h
  · intro h
    have hv : v ∈ M.lowerPositions := hClosed u hu v h
    have hvEq : σ.symm v = v := by
      calc
        σ.symm v = σ.symm (σ v) := by rw [hσ v hv]
        _ = v := σ.symm_apply_apply v
    simpa only [hvEq] using h

/-- The selected top normal form preserves every full C-row from
the already ordered lower closure of an actual local type. -/
theorem CompleteLocalMatrix.normalForm_lower_C_row
    [LinearOrder (CompleteLocalMatrix n)]
    (M : CompleteLocalMatrix n) (hClosed : M.LowerCClosed)
    (u : Fin n) (hu : u ∈ M.lowerPositions) (v : Fin n) :
    (u,v) ∈ M.normalForm.closurePairs ↔
      (u,v) ∈ M.closurePairs := by
  obtain ⟨σ,hσ,hEq⟩ := M.normalForm_exists_permutation
  rw [← hEq]
  exact M.closed_lower_C_row_relabel σ hσ hClosed u hu v

end FiniteUnaryCoordinates
end BigHrushovski
