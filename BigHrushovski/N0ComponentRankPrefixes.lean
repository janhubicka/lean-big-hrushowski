import BigHrushovski.OrientationComponentDownsets
import Mathlib.Tactic

/-!
# Component ranks and strong prefixes in finite orientations

A ranking of strongly connected components is valid if it puts
each component strictly after every proper successor component.
A rank cutoff therefore consists of whole components and is
successor-closed. The predimension lemma then makes the cutoff
strong in the underlying undirected graph.

Rank values need not be consecutive or globally injective. To
count *linear extensions* one will later restrict to injective
rankings with consecutive values on the distinct components.
These lemmas deliberately do not count orders.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- The rank respects every dependency, independently of how the
components have been enumerated. -/
def RespectsComponentDependencies [Fintype V]
    (rank : Finset V → ℕ) : Prop :=
  ∀ B C : Finset V, O.ComponentPrecedes B C → rank B < rank C

/-- Vertices belonging to components of rank strictly below n. -/
noncomputable def componentRankPrefix [Fintype V]
    (rank : Finset V → ℕ) (n : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => rank (O.component x) < n)

theorem mem_componentRankPrefix_iff [Fintype V]
    (rank : Finset V → ℕ) (n : ℕ) (x : V) :
    x ∈ O.componentRankPrefix rank n ↔
    rank (O.component x) < n := by
  classical
  simp only [componentRankPrefix, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem componentRankPrefix_mono [Fintype V]
    (rank : Finset V → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    O.componentRankPrefix rank m ⊆
      O.componentRankPrefix rank n := by
  intro x hx
  rw [O.mem_componentRankPrefix_iff] at hx ⊢
  exact lt_of_lt_of_le hx hmn

/-- Each component is either wholly below the cutoff or
wholly outside the rank prefix. -/
theorem component_subset_rankPrefix [Fintype V]
    (rank : Finset V → ℕ) (n : ℕ)
    {x : V} (hx : rank (O.component x) < n) :
    O.component x ⊆ O.componentRankPrefix rank n := by
  intro y hy
  rw [O.mem_componentRankPrefix_iff]
  have hSame : O.component x = O.component y :=
    O.component_eq_of_stronglyConnected
      ((O.mem_component_iff x y).mp hy)
  rw [← hSame]
  exact hx

/-- Every cutoff of a valid ranking is successor-closed. -/
theorem componentRankPrefix_isSuccessorClosed [Fintype V]
    (rank : Finset V → ℕ)
    (hr : O.RespectsComponentDependencies rank) (n : ℕ) :
    O.IsSuccessorClosed (O.componentRankPrefix rank n) := by
  apply (O.successorClosed_iff_component_downward
    (O.componentRankPrefix rank n)).mpr
  constructor
  · intro x hx y hy
    have hSame : O.component x = O.component y :=
      O.component_eq_of_stronglyConnected
        ((O.mem_component_iff x y).mp hy)
    rw [O.mem_componentRankPrefix_iff] at hx ⊢
    rw [← hSame]
    exact hx
  · intro upper lower hPre hUpper
    rw [O.mem_componentRankPrefix_iff] at hUpper ⊢
    exact lt_trans (hr _ _ hPre) hUpper

/-- In particular, valid component-order prefixes are strong
substructures for the actual graph predimension. -/
theorem componentRankPrefix_isStrong [Fintype V]
    (rank : Finset V → ℕ)
    (hr : O.RespectsComponentDependencies rank) (n : ℕ) :
    O.underlying.toPredimension.IsStrong
      (O.componentRankPrefix rank n) Finset.univ :=
  O.successorClosed_strong
    (Finset.subset_univ _) (O.componentRankPrefix_isSuccessorClosed rank hr n)

end FiniteOrientation
end BigHrushovski
