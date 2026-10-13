import BigHrushovski.C0Components
import BigHrushovski.C0Neighbours

/-!
# Earlier-component dependencies and finite unary closure in C0

The countable minimal strong enumeration has finite nonempty
components B_i, each vertex belonging to exactly one component.

For a component B_i, record the indices of those earlier
components containing an old neighbour of some vertex of B_i.
These indices are all strictly below i. Following these
dependencies therefore never increases the component index.

An inductively defined ancestor relation describes the finite
set of components reachable from a given component by these
back edges. It supplies the unary component closure. The
first important structural property is that mutual membership
of unary closures means membership in the same component.

This module does not assert the functional Fraisse extension
property or any Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteCatalogue

theorem genericC0ComponentIndex_lt_iff_stage (x n : ℕ) :
    genericC0ComponentIndex x < n ↔
      x ∈ genericC0MinimalStage n := by
  constructor
  · intro h
    have hle : genericC0ComponentIndex x + 1 ≤ n := by omega
    exact (genericC0MinimalStrongChain.stage_monotone hle)
      (genericC0ComponentIndex_spec x)
  · intro hx
    by_contra h
    have hle : n ≤ genericC0ComponentIndex x := by omega
    exact genericC0ComponentIndex_not_prior x
      ((genericC0MinimalStrongChain.stage_monotone hle) hx)

/-- Earlier component indices reached by a single back edge from B_n.
All vertices in the old-neighbour sets lie in A_n. -/
noncomputable def genericC0BackComponentIndices (n : ℕ) : Finset ℕ :=
  ((genericC0Component n).biUnion (fun x =>
    genericTwoSparseGraph.oldNeighbours (genericC0MinimalStage n) x)).image
      genericC0ComponentIndex

theorem genericC0BackComponentIndices_lt {n j : ℕ}
    (hj : j ∈ genericC0BackComponentIndices n) : j < n := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨x, _, hOld⟩ := Finset.mem_biUnion.mp hy
  have hStage :
      y ∈ genericC0MinimalStage n :=
    (genericTwoSparseGraph.mem_oldNeighbours_iff
      (genericC0MinimalStage n) x y).mp hOld |>.1
  exact (genericC0ComponentIndex_lt_iff_stage y n).mpr hStage

theorem genericC0BackComponentIndices_of_adj
    {n x y : ℕ}
    (hx : x ∈ genericC0Component n)
    (hy : y ∈ genericC0MinimalStage n)
    (hxy : genericTwoSparseGraph.adj x y) :
    genericC0ComponentIndex y ∈ genericC0BackComponentIndices n := by
  apply Finset.mem_image.mpr
  refine ⟨y, ?_, rfl⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  exact (genericTwoSparseGraph.mem_oldNeighbours_iff
    (genericC0MinimalStage n) x y).mpr ⟨hy, hxy⟩

/-- Reachability along finite decreasing back-edge dependencies,
including the starting component itself. -/
inductive GenericC0Ancestor (root : ℕ) : ℕ → Prop where
  | root : GenericC0Ancestor root root
  | step {j k : ℕ} (hj : GenericC0Ancestor root j)
      (hback : k ∈ genericC0BackComponentIndices j) :
      GenericC0Ancestor root k

theorem GenericC0Ancestor.le {root j : ℕ}
    (h : GenericC0Ancestor root j) : j ≤ root := by
  induction h with
  | root => exact le_rfl
  | @step j k hj hback ih =>
      exact (Nat.le_of_lt (genericC0BackComponentIndices_lt hback)).trans ih

theorem GenericC0Ancestor.trans {i j k : ℕ}
    (hij : GenericC0Ancestor i j)
    (hjk : GenericC0Ancestor j k) :
    GenericC0Ancestor i k := by
  induction hjk with
  | root => exact hij
  | @step j k hprev hback ih =>
      exact GenericC0Ancestor.step ih hback

/-- The finite set of component indices reachable from a component. -/
noncomputable def genericC0AncestorComponents (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (GenericC0Ancestor n)

theorem mem_genericC0AncestorComponents_iff (i j : ℕ) :
    j ∈ genericC0AncestorComponents i ↔
      GenericC0Ancestor i j := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.le), h⟩

theorem genericC0AncestorComponents_self (i : ℕ) :
    i ∈ genericC0AncestorComponents i :=
  (mem_genericC0AncestorComponents_iff i i).mpr
    GenericC0Ancestor.root

theorem genericC0AncestorComponents_downward {i j k : ℕ}
    (hij : j ∈ genericC0AncestorComponents i)
    (hjk : k ∈ genericC0AncestorComponents j) :
    k ∈ genericC0AncestorComponents i := by
  apply (mem_genericC0AncestorComponents_iff i k).mpr
  exact GenericC0Ancestor.trans
    ((mem_genericC0AncestorComponents_iff i j).mp hij)
    ((mem_genericC0AncestorComponents_iff j k).mp hjk)

/-- Finite unary closure of a vertex: all vertices in its own
component and in components reached by successive back edges. -/
noncomputable def genericC0UnaryClosure (v : ℕ) : Finset ℕ :=
  (genericC0AncestorComponents (genericC0ComponentIndex v)).biUnion
    genericC0Component

theorem mem_genericC0UnaryClosure_iff (v w : ℕ) :
    w ∈ genericC0UnaryClosure v ↔
      GenericC0Ancestor (genericC0ComponentIndex v)
        (genericC0ComponentIndex w) := by
  constructor
  · intro h
    obtain ⟨j, hj, hw⟩ := Finset.mem_biUnion.mp h
    have hidx : genericC0ComponentIndex w = j :=
      (genericC0ComponentIndex_eq_iff w j).mpr hw
    simpa only [hidx] using
      ((mem_genericC0AncestorComponents_iff _ _).mp hj)
  · intro h
    exact Finset.mem_biUnion.mpr
      ⟨genericC0ComponentIndex w,
       (mem_genericC0AncestorComponents_iff _ _).mpr h,
       genericC0ComponentIndex_mem w⟩

theorem genericC0UnaryClosure_self (v : ℕ) :
    v ∈ genericC0UnaryClosure v :=
  (mem_genericC0UnaryClosure_iff v v).mpr
    GenericC0Ancestor.root

theorem genericC0UnaryClosure_trans {u v w : ℕ}
    (hv : v ∈ genericC0UnaryClosure u)
    (hw : w ∈ genericC0UnaryClosure v) :
    w ∈ genericC0UnaryClosure u :=
  (mem_genericC0UnaryClosure_iff u w).mpr
    (GenericC0Ancestor.trans
      ((mem_genericC0UnaryClosure_iff u v).mp hv)
      ((mem_genericC0UnaryClosure_iff v w).mp hw))

theorem genericC0UnaryClosure_nested {u v : ℕ}
    (hv : v ∈ genericC0UnaryClosure u) :
    genericC0UnaryClosure v ⊆ genericC0UnaryClosure u := by
  intro w hw
  exact genericC0UnaryClosure_trans hv hw

/-- Every vertex in the new component shares its entire component. -/
theorem genericC0UnaryClosure_contains_component (v : ℕ) :
    genericC0Component (genericC0ComponentIndex v) ⊆
      genericC0UnaryClosure v := by
  intro w hw
  have heq : genericC0ComponentIndex w = genericC0ComponentIndex v :=
    (genericC0ComponentIndex_eq_iff w _).mpr hw
  exact (mem_genericC0UnaryClosure_iff v w).mpr (by
    rw [heq]
    exact GenericC0Ancestor.root)

/-- The manuscript's mutual-reachability criterion recovers the
original component rather than a larger strongly connected set. -/
theorem genericC0SameComponent_iff_mutual (v w : ℕ) :
    genericC0ComponentIndex v = genericC0ComponentIndex w ↔
      (w ∈ genericC0UnaryClosure v ∧
       v ∈ genericC0UnaryClosure w) := by
  constructor
  · intro heq
    constructor
    · exact (mem_genericC0UnaryClosure_iff v w).mpr (by
        rw [heq]
        exact GenericC0Ancestor.root)
    · exact (mem_genericC0UnaryClosure_iff w v).mpr (by
        rw [← heq]
        exact GenericC0Ancestor.root)
  · rintro ⟨hw, hv⟩
    have hle : genericC0ComponentIndex w ≤ genericC0ComponentIndex v :=
      ((mem_genericC0UnaryClosure_iff v w).mp hw).le
    have hge : genericC0ComponentIndex v ≤ genericC0ComponentIndex w :=
      ((mem_genericC0UnaryClosure_iff w v).mp hv).le
    exact Nat.le_antisymm hge hle

theorem genericC0Component_mem_iff_mutual (v w : ℕ) :
    w ∈ genericC0Component (genericC0ComponentIndex v) ↔
      (w ∈ genericC0UnaryClosure v ∧
       v ∈ genericC0UnaryClosure w) := by
  rw [← genericC0SameComponent_iff_mutual]
  exact (genericC0ComponentIndex_eq_iff w
    (genericC0ComponentIndex v)).symm

/-- The closure includes the back neighbour of any vertex already
included in a reachable component. -/
theorem genericC0UnaryClosure_oldNeighbour {u v w : ℕ}
    (hv : v ∈ genericC0UnaryClosure u)
    (hw : w ∈ genericTwoSparseGraph.oldNeighbours
      (genericC0MinimalStage (genericC0ComponentIndex v)) v) :
    w ∈ genericC0UnaryClosure u := by
  have hb : v ∈ genericC0Component (genericC0ComponentIndex v) :=
    genericC0ComponentIndex_mem v
  have hold := (genericTwoSparseGraph.mem_oldNeighbours_iff
    (genericC0MinimalStage (genericC0ComponentIndex v)) v w).mp hw
  have hback : genericC0ComponentIndex w ∈
      genericC0BackComponentIndices (genericC0ComponentIndex v) :=
    genericC0BackComponentIndices_of_adj hb hold.1 hold.2
  have hanc : GenericC0Ancestor
      (genericC0ComponentIndex v) (genericC0ComponentIndex w) :=
    GenericC0Ancestor.step GenericC0Ancestor.root hback
  exact (mem_genericC0UnaryClosure_iff u w).mpr
    (GenericC0Ancestor.trans
      ((mem_genericC0UnaryClosure_iff u v).mp hv) hanc)

end FiniteCatalogue
end BigHrushovski
