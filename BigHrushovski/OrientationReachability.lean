import BigHrushovski.OrientationRelativeStrong
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Directed reachability and strong components of a 2-orientation

The reflexive transitive closure of the arrow relation generates the
finite successor closure.  Mutual reachability defines the strongly
connected components used in the N₀ degree formula.  These statements
hold for any orientation, including directed cycles.

The module proves no big Ramsey degree or recurrence theorem.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- An oriented path of length zero or more. -/
def Reaches (x y : V) : Prop :=
  Relation.ReflTransGen (fun u v => v ∈ O.out u) x y

theorem reaches_refl (x : V) : O.Reaches x x :=
  Relation.ReflTransGen.refl

theorem reaches_arrow {x y : V} (hxy : y ∈ O.out x) :
    O.Reaches x y :=
  Relation.ReflTransGen.single hxy

theorem reaches_trans {x y z : V}
    (hxy : O.Reaches x y) (hyz : O.Reaches y z) :
    O.Reaches x z :=
  Relation.ReflTransGen.trans hxy hyz

/-- A successor-closed set contains the whole directed path
starting at any of its vertices. -/
theorem successorClosed_of_reaches {s : Finset V} {x y : V}
    (hs : O.IsSuccessorClosed s)
    (hx : x ∈ s) (hxy : O.Reaches x y) : y ∈ s := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact hs _ ih hstep

/-- The equivalence relation of belonging to one strongly
connected component. -/
def StronglyConnected (x y : V) : Prop :=
  O.Reaches x y ∧ O.Reaches y x

theorem stronglyConnected_refl (x : V) : O.StronglyConnected x x :=
  ⟨O.reaches_refl x, O.reaches_refl x⟩

theorem stronglyConnected_symm {x y : V}
    (hxy : O.StronglyConnected x y) :
    O.StronglyConnected y x :=
  ⟨hxy.2, hxy.1⟩

theorem stronglyConnected_trans {x y z : V}
    (hxy : O.StronglyConnected x y)
    (hyz : O.StronglyConnected y z) :
    O.StronglyConnected x z :=
  ⟨O.reaches_trans hxy.1 hyz.1,
   O.reaches_trans hyz.2 hxy.2⟩

/-- The finite set of vertices reachable from a finite generator set.
This requires a finite ambient domain but no acyclicity. -/
noncomputable def successorClosure [Fintype V]
    (s : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => ∃ x ∈ s, O.Reaches x y)

theorem mem_successorClosure_iff [Fintype V]
    (s : Finset V) (y : V) :
    y ∈ O.successorClosure s ↔
      ∃ x ∈ s, O.Reaches x y := by
  classical
  simp only [successorClosure, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem subset_successorClosure [Fintype V]
    (s : Finset V) : s ⊆ O.successorClosure s := by
  intro x hx
  exact (O.mem_successorClosure_iff s x).mpr
    ⟨x, hx, O.reaches_refl x⟩

theorem successorClosure_mono [Fintype V]
    {s t : Finset V} (hst : s ⊆ t) :
    O.successorClosure s ⊆ O.successorClosure t := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ :=
    (O.mem_successorClosure_iff s y).mp hy
  exact (O.mem_successorClosure_iff t y).mpr
    ⟨x, hst hx, hxy⟩

theorem successorClosure_isClosed [Fintype V]
    (s : Finset V) :
    O.IsSuccessorClosed (O.successorClosure s) := by
  intro x hx y hxy
  obtain ⟨u, hu, hux⟩ :=
    (O.mem_successorClosure_iff s x).mp hx
  exact (O.mem_successorClosure_iff s y).mpr
    ⟨u, hu, O.reaches_trans hux (O.reaches_arrow hxy)⟩

/-- This is the least successor-closed set containing s. -/
theorem successorClosure_minimal [Fintype V]
    {s t : Finset V} (hst : s ⊆ t)
    (ht : O.IsSuccessorClosed t) :
    O.successorClosure s ⊆ t := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ :=
    (O.mem_successorClosure_iff s y).mp hy
  exact O.successorClosed_of_reaches ht (hst hx) hxy

theorem successorClosure_eq_of_closed [Fintype V]
    {s : Finset V} (hs : O.IsSuccessorClosed s) :
    O.successorClosure s = s := by
  apply Finset.Subset.antisymm
  · exact O.successorClosure_minimal (by intro x hx; exact hx) hs
  · exact O.subset_successorClosure s

theorem successorClosure_idempotent [Fintype V]
    (s : Finset V) :
    O.successorClosure (O.successorClosure s) =
      O.successorClosure s :=
  O.successorClosure_eq_of_closed (O.successorClosure_isClosed s)

/-- Every finitely generated successor closure is a strong
substructure of every finite container containing it. -/
theorem successorClosure_strong [Fintype V]
    {s t : Finset V}
    (hst : O.successorClosure s ⊆ t) :
    O.underlying.toPredimension.IsStrong
      (O.successorClosure s) t :=
  O.successorClosed_strong hst (O.successorClosure_isClosed s)

/-- The SCC containing a vertex in a finite orientation. -/
noncomputable def component [Fintype V]
    (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => O.StronglyConnected x y)

theorem mem_component_iff [Fintype V] (x y : V) :
    y ∈ O.component x ↔ O.StronglyConnected x y := by
  classical
  simp only [component, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem self_mem_component [Fintype V]
    (x : V) : x ∈ O.component x :=
  (O.mem_component_iff x x).mpr (O.stronglyConnected_refl x)

/-- Strongly connected vertices have literally equal components. -/
theorem component_eq_of_stronglyConnected [Fintype V]
    {x y : V} (hxy : O.StronglyConnected x y) :
    O.component x = O.component y := by
  ext z
  rw [O.mem_component_iff x z, O.mem_component_iff y z]
  constructor
  · intro hxz
    exact ⟨O.reaches_trans hxy.2 hxz.1,
           O.reaches_trans hxz.2 hxy.1⟩
  · intro hyz
    exact ⟨O.reaches_trans hxy.1 hyz.1,
           O.reaches_trans hyz.2 hxy.2⟩

theorem stronglyConnected_iff_component_eq [Fintype V]
    (x y : V) :
    O.StronglyConnected x y ↔ O.component x = O.component y := by
  constructor
  · exact O.component_eq_of_stronglyConnected
  · intro heq
    have hy : y ∈ O.component y := O.self_mem_component y
    rw [← heq] at hy
    exact (O.mem_component_iff x y).mp hy

theorem component_subset_successorClosure [Fintype V]
    (x : V) :
    O.component x ⊆ O.successorClosure ({x} : Finset V) := by
  intro y hy
  have hxy := (O.mem_component_iff x y).mp hy
  exact (O.mem_successorClosure_iff ({x} : Finset V) y).mpr
    ⟨x, by simp, hxy.1⟩

end FiniteOrientation
end BigHrushovski
