import BigHrushovski.CFDClosedHull

/-!
# Predimension does not increase under finite strict d-closure

For a finite generating set A in a finite ambient C, consider
all supersets Y of A whose predimension is at most δ(A).
Choose one with the largest possible cardinality. It is
strictly d-closed: a proper enlargement of no greater
predimension would be another candidate of larger size.

Thus there is a strictly d-closed superset Y of A with
δ(Y) ≤ δ(A). The least strict d-closed hull H of A lies
inside Y. Since H is d-closed in the ambient C, it is
d-closed in Y, whence δ(H) ≤ δ(Y) ≤ δ(A).

The maximal-cardinality proof is simpler than a separate
minimum-predimension construction. It does not use any
graph-specific calculation or growth function. Submodularity
is needed only by the pre-existing intersection theorem
which makes the least d-closed hull itself d-closed.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- A finite set A has a strictly d-closed superset in C
of predimension at most δ(A). Choose a largest superset
among all those satisfying the predimension bound. -/
theorem exists_dClosed_superset_delta_le
    {a c : Finset V} (hac : a ⊆ c) :
    ∃ y : Finset V,
      a ⊆ y ∧ d.IsDClosed y c ∧ d.delta y ≤ d.delta a := by
  classical
  let candidates : Finset (Finset V) :=
    c.powerset.filter (fun y => a ⊆ y ∧ d.delta y ≤ d.delta a)
  have hACand : a ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hac, Finset.Subset.rfl, le_rfl⟩
  let sizes : Finset ℕ := candidates.image Finset.card
  have hSizes : sizes.Nonempty := by
    exact ⟨a.card, Finset.mem_image.mpr ⟨a, hACand, rfl⟩⟩
  have hMaxMem : sizes.max' hSizes ∈ sizes :=
    Finset.max'_mem sizes hSizes
  obtain ⟨y, hyCand, hyCard⟩ := Finset.mem_image.mp hMaxMem
  obtain ⟨hySubC, hay, hyDelta⟩ :
      y ⊆ c ∧ a ⊆ y ∧ d.delta y ≤ d.delta a := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset]
      using hyCand
  have hyClosed : d.IsDClosed y c := by
    refine ⟨hySubC, ?_⟩
    intro z hyz hne hzc
    by_contra hbad
    have hzDeltaY : d.delta z ≤ d.delta y :=
      le_of_not_gt hbad
    have hzCand : z ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hzc, hay.trans hyz, hzDeltaY.trans hyDelta⟩
    have hzCard : z.card ∈ sizes :=
      Finset.mem_image.mpr ⟨z, hzCand, rfl⟩
    have hzCardLe : z.card ≤ sizes.max' hSizes :=
      Finset.le_max' sizes z.card hzCard
    have hProper : y ⊂ z :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hyz, by intro heq; exact hne heq.symm⟩
    have hCardLt : y.card < z.card :=
      Finset.card_lt_card hProper
    omega
  exact ⟨y, hay, hyClosed, hyDelta⟩

/-- The least finite strictly d-closed hull has predimension
at most that of its original generating set. -/
theorem delta_dClosedHull_le
    {a c : Finset V} (hac : a ⊆ c) :
    d.delta (d.dClosedHull a c) ≤ d.delta a := by
  obtain ⟨y, hay, hyClosed, hyDelta⟩ :=
    d.exists_dClosed_superset_delta_le hac
  have hHullSub : d.dClosedHull a c ⊆ y :=
    d.dClosedHull_least hay hyClosed
  have hHullClosed : d.IsDClosed (d.dClosedHull a c) c :=
    d.dClosedHull_dclosed a c
  have hHullClosedY : d.IsDClosed (d.dClosedHull a c) y :=
    d.dclosed_restrict hHullClosed hHullSub hyClosed.1
  have hDeltaHullY : d.delta (d.dClosedHull a c) ≤ d.delta y :=
    (d.strong_of_dClosed hHullClosedY).2 y hHullSub Finset.Subset.rfl
  exact hDeltaHullY.trans hyDelta

end Predimension
end BigHrushovski
