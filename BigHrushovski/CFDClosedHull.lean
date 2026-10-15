import BigHrushovski.CFDClosedDecomposition
import BigHrushovski.Closure

/-!
# Least strict d-closed hull inside a finite ambient graph

Construct the least d-closed vertex set containing a given finite
set by intersecting all ambient d-closed supersets. No countable
genericity, enumeration or uniform closure bound is required.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Finite intersections of d-closed substructures are d-closed. -/
theorem dclosed_intersectFamily (d : Predimension V) (c : Finset V)
    (fs : Finset (Finset V))
    (hfs : ∀ b ∈ fs, d.IsDClosed b c) :
    d.IsDClosed (intersectFamily c fs) c := by
  classical
  induction fs using Finset.induction_on with
  | empty =>
      simpa [intersectFamily_empty] using d.dclosed_refl c
  | @insert b fs hnot ih =>
      have hb : d.IsDClosed b c := hfs b (Finset.mem_insert_self b fs)
      have hrest : ∀ t ∈ fs, d.IsDClosed t c := by
        intro t ht
        exact hfs t (Finset.mem_insert_of_mem ht)
      rw [intersectFamily_insert]
      exact d.dclosed_inter (ih hrest) hb

/-- Least d-closed subset of a finite ambient set containing a. -/
noncomputable def dClosedHull (d : Predimension V)
    (a c : Finset V) : Finset V := by
  classical
  exact intersectFamily c
    (c.powerset.filter (fun b => a ⊆ b ∧ d.IsDClosed b c))

theorem dClosedHull_dclosed (d : Predimension V) (a c : Finset V) :
    d.IsDClosed (d.dClosedHull a c) c := by
  classical
  unfold dClosedHull
  apply d.dclosed_intersectFamily
  intro b hb
  exact (Finset.mem_filter.mp hb).2.2

theorem subset_dClosedHull (d : Predimension V) {a c : Finset V}
    (hac : a ⊆ c) : a ⊆ d.dClosedHull a c := by
  classical
  intro v hv
  change v ∈ intersectFamily c
    (c.powerset.filter (fun b => a ⊆ b ∧ d.IsDClosed b c))
  apply Finset.mem_filter.mpr
  refine ⟨hac hv, ?_⟩
  intro b hb
  exact (Finset.mem_filter.mp hb).2.1 hv

theorem dClosedHull_least (d : Predimension V) {a b c : Finset V}
    (hab : a ⊆ b) (hbc : d.IsDClosed b c) :
    d.dClosedHull a c ⊆ b := by
  classical
  intro v hv
  have hmem : b ∈ c.powerset.filter (fun t => a ⊆ t ∧ d.IsDClosed t c) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hbc.1, ⟨hab, hbc⟩⟩
  exact (Finset.mem_filter.mp hv).2 b hmem

theorem exists_least_dClosed_hull (d : Predimension V)
    {a c : Finset V} (hac : a ⊆ c) :
    ∃ h : Finset V, a ⊆ h ∧ d.IsDClosed h c ∧
      ∀ b : Finset V, a ⊆ b → d.IsDClosed b c → h ⊆ b := by
  exact ⟨d.dClosedHull a c, d.subset_dClosedHull hac,
    d.dClosedHull_dclosed a c, fun b hab hbc => d.dClosedHull_least hab hbc⟩

end Predimension
end BigHrushovski
