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
    omega

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

end FiniteC0
end BigHrushovski
