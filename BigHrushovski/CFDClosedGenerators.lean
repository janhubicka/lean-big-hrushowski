import BigHrushovski.CFDClosedHull

/-!
# Every point in a finite minimal d-closed increment generates it

For a finite d-closed extension a ≤d b, no proper intermediate
d-closed structure exists exactly when every new vertex x generates
all of b together with a. This is the finite closure argument used
to select the blocks of the C_F level construction.

All hulls are computed in the explicitly named finite ambient b.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- In a minimal d-closed step, every new vertex generates the
entire endpoint by d-closure over the old base. -/
theorem minimalDClosedStep_every_generator
    {a b : Finset V}
    (hMin : d.IsMinimalDClosedStep a b)
    {x : V} (hxb : x ∈ b) (hxna : x ∉ a) :
    d.dClosedHull (insert x a) b = b := by
  have hInsert : insert x a ⊆ b := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvA
    · exact hxb
    · exact hMin.1.1 hvA
  have hHullClosed : d.IsDClosed
      (d.dClosedHull (insert x a) b) b :=
    d.dClosedHull_dclosed (insert x a) b
  have hAHull : a ⊆ d.dClosedHull (insert x a) b := by
    intro v hv
    exact d.subset_dClosedHull hInsert
      (Finset.mem_insert_of_mem hv)
  have hXHull : x ∈ d.dClosedHull (insert x a) b :=
    d.subset_dClosedHull hInsert
      (Finset.mem_insert_self x a)
  rcases hMin.2.2 (d.dClosedHull (insert x a) b)
      hAHull hHullClosed.1 hHullClosed with hEq | hEq
  · have hXa : x ∈ a := by
      rw [← hEq]
      exact hXHull
    exact (hxna hXa).elim
  · exact hEq

/-- Converse: a d-closed step with every new point generating
the endpoint admits no proper d-closed intermediate structure. -/
theorem minimalDClosedStep_of_every_generator
    {a b : Finset V}
    (hab : d.IsDClosed a b) (hne : a ≠ b)
    (hGen : ∀ x : V, x ∈ b → x ∉ a →
      d.dClosedHull (insert x a) b = b) :
    d.IsMinimalDClosedStep a b := by
  refine ⟨hab, hne, ?_⟩
  intro z haz hzb hzClosed
  by_cases hza : z = a
  · exact Or.inl hza
  · right
    have hExists : ∃ x : V, x ∈ z ∧ x ∉ a := by
      by_contra hNot
      have hzaSub : z ⊆ a := by
        intro x hxz
        by_contra hxna
        exact hNot ⟨x, hxz, hxna⟩
      exact hza (le_antisymm hzaSub haz)
    obtain ⟨x, hxz, hxna⟩ := hExists
    have hInsert : insert x a ⊆ z := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hva
      · exact hxz
      · exact haz hva
    have hHullSub : d.dClosedHull (insert x a) b ⊆ z :=
      d.dClosedHull_least hInsert hzClosed
    have hEqHull : d.dClosedHull (insert x a) b = b :=
      hGen x (hzb hxz) hxna
    rw [hEqHull] at hHullSub
    exact le_antisymm hzb hHullSub

/-- Finite minimal d-closed steps are precisely those where each
new vertex generates the whole endpoint over the old base. -/
theorem minimalDClosedStep_iff_every_generator
    {a b : Finset V}
    (hab : d.IsDClosed a b) (hne : a ≠ b) :
    d.IsMinimalDClosedStep a b ↔
      ∀ x : V, x ∈ b → x ∉ a →
        d.dClosedHull (insert x a) b = b := by
  constructor
  · intro hMin x hx hxna
    exact d.minimalDClosedStep_every_generator hMin hx hxna
  · exact d.minimalDClosedStep_of_every_generator hab hne

end Predimension
end BigHrushovski
