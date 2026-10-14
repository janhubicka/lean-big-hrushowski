import BigHrushovski.C0OrientationInvariantValues

/-!
# Move a finite C0-closed component ideal before the remaining components

A canonical finite C0 presentation κ:V→Fin n contains a closed
vertex set S which may not be an initial segment of its witnessing
component order. There is no need to align orders of common
components by arbitrary adjacent swaps.

Instead give the vertices of S their original indices < n,
and all vertices outside S the later indices n+κ(v). This
puts S first, preserving the relative order within S and
within its complement. The full named unary function remains
identical: closedness of S forces every graph edge crossing
from S to its complement to point to the *earlier* S
component, before and after this rearrangement.

The induced component partition and orientation of every
intercomponent graph edge are unchanged, so the certified
orientation-invariance theorem preserves complete unary
closures, not merely immediate predecessors.

This module proves the chronological and unary-value
identities. Preservation of minimal strong steps in the
reordered presentation is the next separate lemma.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n : ℕ}

/-- The old component index on a closed set, and a later shifted
index for every vertex in its complement. -/
noncomputable def frontloadIndex
    (κ : V → Fin n) (s : Finset V) (v : V) : Fin (n+n) :=
  if hv : v ∈ s then
    ⟨(κ v).val, by omega⟩
  else
    ⟨n+(κ v).val, by omega⟩

theorem frontloadIndex_inside
    (κ : V → Fin n) (s : Finset V) (v : V) (hv : v ∈ s) :
    (frontloadIndex κ s v).val = (κ v).val := by
  simp [frontloadIndex, hv]

theorem frontloadIndex_outside
    (κ : V → Fin n) (s : Finset V) (v : V) (hv : v ∉ s) :
    (frontloadIndex κ s v).val = n + (κ v).val := by
  simp [frontloadIndex, hv]

/-- Two vertices of the same original component are either
both in a unary-closed set or both outside it. -/
theorem closed_mem_iff_of_same_component
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u v : V) (hSame : κ u = κ v) :
    u ∈ s ↔ v ∈ s := by
  constructor
  · intro hu
    have hvValue : v ∈ canonicalValue G κ u := by
      apply (mem_canonicalValue_iff G κ u v).mpr
      rw [hSame]
      exact TaggedAmalgam.DependencyAncestor.root
    exact hClosed u hu hvValue
  · intro hv
    have huValue : u ∈ canonicalValue G κ v := by
      apply (mem_canonicalValue_iff G κ v u).mpr
      rw [← hSame]
      exact TaggedAmalgam.DependencyAncestor.root
    exact hClosed v hv huValue

/-- Every edge crossing from S to its complement has its
S endpoint in an earlier component: otherwise the
backward closure of that endpoint would leave S. -/
theorem closed_cross_edge_points_outward
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u v : V) (hu : u ∈ s) (hv : v ∉ s)
    (hAdj : G.adj u v) :
    (κ u).val < (κ v).val := by
  by_contra hNo
  have hLe : (κ v).val ≤ (κ u).val := by omega
  have hPath : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ u) (κ v) := by
    by_cases heq : κ u = κ v
    · rw [← heq]
      exact TaggedAmalgam.DependencyAncestor.root
    · have hLt : (κ v).val < (κ u).val := by
        have hNe : (κ v).val ≠ (κ u).val := by
          intro hVal
          exact heq (Fin.ext hVal.symm)
        omega
      exact TaggedAmalgam.DependencyAncestor.step
        TaggedAmalgam.DependencyAncestor.root
        ⟨hLt,u,v,rfl,rfl,hAdj⟩
  have hvValue : v ∈ canonicalValue G κ u :=
    (mem_canonicalValue_iff G κ u v).mpr hPath
  exact hv (hClosed u hu hvValue)

/-- A closed-base frontloading preserves exactly the partition
of vertices into complete components, without identifying
different components or cutting an existing one. -/
theorem frontloadIndex_same_components
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u v : V) :
    κ u = κ v ↔ frontloadIndex κ s u = frontloadIndex κ s v := by
  constructor
  · intro hEq
    have hMember :=
      closed_mem_iff_of_same_component G κ s hClosed u v hEq
    by_cases hu : u ∈ s
    · have hv : v ∈ s := hMember.mp hu
      apply Fin.ext
      rw [frontloadIndex_inside κ s u hu,
          frontloadIndex_inside κ s v hv, hEq]
    · have hv : v ∉ s := by
        intro hvs
        exact hu (hMember.mpr hvs)
      apply Fin.ext
      rw [frontloadIndex_outside κ s u hu,
          frontloadIndex_outside κ s v hv, hEq]
  · intro hEq
    have hNum := congrArg Fin.val hEq
    apply Fin.ext
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
    · rw [frontloadIndex_inside κ s u hu,
          frontloadIndex_inside κ s v hv] at hNum
      exact hNum
    · rw [frontloadIndex_inside κ s u hu,
          frontloadIndex_outside κ s v hv] at hNum
      have hBound := (κ u).isLt
      omega
    · rw [frontloadIndex_outside κ s u hu,
          frontloadIndex_inside κ s v hv] at hNum
      have hBound := (κ v).isLt
      omega
    · rw [frontloadIndex_outside κ s u hu,
          frontloadIndex_outside κ s v hv] at hNum
      omega

/-- All graph-edge orientations between distinct components
remain exactly the same after frontloading a closed base. -/
theorem frontloadIndex_preserves_edge_orientation
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u v : V) (hAdj : G.adj u v) :
    ((κ u).val < (κ v).val ↔
      (frontloadIndex κ s u).val <
        (frontloadIndex κ s v).val) := by
  by_cases hu : u ∈ s <;> by_cases hv : v ∈ s
  · rw [frontloadIndex_inside κ s u hu,
        frontloadIndex_inside κ s v hv]
  · have hOld := closed_cross_edge_points_outward
      G κ s hClosed u v hu hv hAdj
    rw [frontloadIndex_inside κ s u hu,
        frontloadIndex_outside κ s v hv]
    constructor
    · intro _
      have hBound := (κ u).isLt
      omega
    · intro _
      exact hOld
  · have hOld := closed_cross_edge_points_outward
      G κ s hClosed v u hv hu (G.symm u v hAdj)
    rw [frontloadIndex_outside κ s u hu,
        frontloadIndex_inside κ s v hv]
    constructor <;> intro h <;> omega
  · rw [frontloadIndex_outside κ s u hu,
        frontloadIndex_outside κ s v hv]
    omega

/-- Moving a complete unary-closed component ideal to the
front changes no canonical set-valued unary function values. -/
theorem canonicalValue_frontload_eq
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (u : V) :
    canonicalValue G (frontloadIndex κ s) u =
      canonicalValue G κ u := by
  symm
  exact canonicalValue_eq_of_component_partition_and_edge_orientation
    G κ (frontloadIndex κ s)
    (frontloadIndex_same_components G κ s hClosed)
    (frontloadIndex_preserves_edge_orientation G κ s hClosed)
    u

/-- The first n stages are precisely the old chronological
cuts restricted to the selected closed base. -/
theorem oldStage_frontload_first
    (κ : V → Fin n) (s : Finset V) (k : ℕ)
    (hk : k ≤ n) :
    oldStage (frontloadIndex κ s) k =
      s ∩ oldStage κ k := by
  classical
  ext v
  simp only [mem_oldStage_iff, Finset.mem_inter]
  by_cases hv : v ∈ s
  · simp [frontloadIndex_inside κ s v hv, hv]
  · simp [frontloadIndex_outside κ s v hv, hv]

/-- The first stage after the frontloaded part is exactly S. -/
theorem oldStage_frontload_boundary
    (κ : V → Fin n) (s : Finset V) :
    oldStage (frontloadIndex κ s) n = s := by
  rw [oldStage_frontload_first κ s n (le_refl n),
    oldStage_final κ]
  exact Finset.inter_univ s

/-- After stage n, the old selected base is present and
the remaining components enter in their original order. -/
theorem oldStage_frontload_after
    (κ : V → Fin n) (s : Finset V) (j : ℕ) :
    oldStage (frontloadIndex κ s) (n+j) =
      s ∪ oldStage κ j := by
  classical
  ext v
  simp only [mem_oldStage_iff, Finset.mem_union]
  by_cases hv : v ∈ s
  · simp [frontloadIndex_inside κ s v hv, hv]
    have hBound := (κ v).isLt
    omega
  · simp [frontloadIndex_outside κ s v hv, hv]
    omega


/-- Moving a finite unary-closed component ideal to the beginning
of a minimal-strong presentation preserves every nonempty minimal
step. In the first half, the selected components keep the
minimal-step property by closed-set heredity; in the second half,
the remaining components retain minimality under the extra old
base S because there are no edges to the newly earlier selected
components outside their original old prefix. -/
theorem frontloadIndex_minimal_steps
    (G : GraphOn V) (κ : V → Fin n)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s)
    (hOld : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) :
    ∀ k : ℕ, k < n+n →
      oldStage (frontloadIndex κ s) k =
        oldStage (frontloadIndex κ s) (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage (frontloadIndex κ s) k)
        (oldStage (frontloadIndex κ s) (k+1)) := by
  classical
  intro k hk
  by_cases hkFirst : k < n
  · -- Restrict the original minimal steps to the closed base.
    rcases hOld k hkFirst with hEq | hMin
    · left
      rw [oldStage_frontload_first κ s k (by omega),
        oldStage_frontload_first κ s (k+1) (by omega), hEq]
    · have hWhole : ∀ u ∈ component κ k,
          component κ k ⊆ canonicalValue G κ u := by
        intro u hu
        exact canonicalValue_contains_component G κ k hu
      rcases G.closedUnderValues_block_dichotomy
        (canonicalValue G κ) s (component κ k)
        hClosed hWhole with hAll | hNone
      · have hEqCut :
            s ∩ oldStage κ (k+1) =
              (s ∩ oldStage κ k) ∪ component κ k := by
          rw [oldStage_succ κ k]
          ext v
          simp only [Finset.mem_inter,Finset.mem_union]
          constructor
          · rintro ⟨hvS, hv⟩
            rcases hv with hOldV | hB
            · exact Or.inl ⟨hvS,hOldV⟩
            · exact Or.inr hB
          · rintro (⟨hvS,hOldV⟩ | hB)
            · exact ⟨hvS,Or.inl hOldV⟩
            · exact ⟨hAll hB,Or.inr hB⟩
        have hNo :
            G.NoCrossEdges (oldStage κ k)
              ((s ∩ oldStage κ k) ∪ component κ k) := by
          apply G.closedUnderValues_block_noCross
            (canonicalValue G κ) s
            (oldStage κ k) (component κ k)
            hClosed
          · intro u hu v hv ha
            exact canonicalValue_oldNeighbour G κ k hu hv ha
          · exact hAll
        have hOriginal : G.toPredimension.IsMinimalStrongStep
            (oldStage κ k)
            (oldStage κ k ∪ component κ k) := by
          rw [oldStage_succ κ k] at hMin
          exact hMin
        have hLift : G.toPredimension.IsMinimalStrongStep
            (s ∩ oldStage κ k)
            ((s ∩ oldStage κ k) ∪ component κ k) :=
          G.minimalStrongStep_local_of_noCross
            (s ∩ oldStage κ k) (oldStage κ k)
            (component κ k) Finset.inter_subset_right
            (oldStage_disjoint_component κ k) hNo hOriginal
        right
        rw [oldStage_frontload_first κ s k (by omega),
          oldStage_frontload_first κ s (k+1) (by omega),
          hEqCut]
        exact hLift
      · left
        have hEqCut : s ∩ oldStage κ (k+1) =
            s ∩ oldStage κ k := by
          rw [oldStage_succ κ k]
          ext v
          simp only [Finset.mem_inter,Finset.mem_union]
          constructor
          · rintro ⟨hvS,hv⟩
            rcases hv with hvOld | hvB
            · exact ⟨hvS,hvOld⟩
            · exact False.elim
                ((Finset.disjoint_left.mp hNone) hvS hvB)
          · rintro ⟨hvS,hvOld⟩
            exact ⟨hvS,Or.inl hvOld⟩
        rw [oldStage_frontload_first κ s k (by omega),
          oldStage_frontload_first κ s (k+1) (by omega),
          hEqCut]
  · let j := k-n
    have hj : j < n := by omega
    have hK : k = n+j := by omega
    rcases hOld j hj with hEq | hMin
    · left
      rw [hK, oldStage_frontload_after κ s j,
        show n+j+1 = n+(j+1) by omega,
        oldStage_frontload_after κ s (j+1), hEq]
    · let A := oldStage κ j
      let B := component κ j
      have hWhole : ∀ u ∈ B, B ⊆ canonicalValue G κ u := by
        intro u hu
        exact canonicalValue_contains_component G κ j hu
      rcases G.closedUnderValues_block_dichotomy
        (canonicalValue G κ) s B hClosed hWhole with hAll | hNone
      · left
        have hAbsorb : s ∪ oldStage κ j =
            s ∪ oldStage κ (j+1) := by
          rw [oldStage_succ κ j]
          ext v
          simp only [Finset.mem_union]
          constructor
          · rintro (hS | hOldV)
            · exact Or.inl hS
            · exact Or.inr (Or.inl hOldV)
          · rintro (hS | (hOldV | hB))
            · exact Or.inl hS
            · exact Or.inr hOldV
            · exact Or.inl (hAll hB)
        rw [hK, oldStage_frontload_after κ s j,
          show n+j+1 = n+(j+1) by omega,
          oldStage_frontload_after κ s (j+1),
          hAbsorb]
      · right
        have hDisj : Disjoint (s ∪ A) B := by
          apply Finset.disjoint_left.mpr
          intro v hv hvB
          rcases Finset.mem_union.mp hv with hvS | hvA
          · exact (Finset.disjoint_left.mp hNone) hvS hvB
          · exact (Finset.disjoint_left.mp
              (oldStage_disjoint_component κ j)) hvA hvB
        have hNo : G.NoCrossEdges (s ∪ A) (A ∪ B) := by
          apply G.noCross_of_backNeighbours (s ∪ A) A B
            Finset.subset_union_right
          intro u huB v hvOld hAdj
          rcases Finset.mem_union.mp hvOld with hvS | hvA
          · have huNotS : u ∉ s := by
              intro huS
              exact (Finset.disjoint_left.mp hNone) huS huB
            have hEarlier : (κ v).val < (κ u).val :=
              closed_cross_edge_points_outward
                G κ s hClosed v u hvS huNotS
                (G.symm u v hAdj)
            have huIndex : (κ u).val = j :=
              (mem_component_iff κ j u).mp huB
            exact (mem_oldStage_iff κ j v).mpr (by omega)
          · exact hvA
        have hOriginal : G.toPredimension.IsMinimalStrongStep
            A (A ∪ B) := by
          rw [oldStage_succ κ j] at hMin
          exact hMin
        have hLift : G.toPredimension.IsMinimalStrongStep
            (s ∪ A) ((s ∪ A) ∪ B) :=
          G.minimalStrongStep_enlarged_of_local
            A (s ∪ A) B Finset.subset_union_right
            hDisj hNo hOriginal
        rw [hK, oldStage_frontload_after κ s j,
          show n+j+1 = n+(j+1) by omega,
          oldStage_frontload_after κ s (j+1),
          oldStage_succ κ j]
        simpa only [Finset.union_assoc] using hLift


end FiniteC0
end BigHrushovski
