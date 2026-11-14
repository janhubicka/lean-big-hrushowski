import BigHrushovski.CFRealGrowthRestriction
import BigHrushovski.CFDClosedHullDelta
import BigHrushovski.CFDClosedChain

/-!
# Uniformly bounded global strict d-closures from growth inequalities

A finite strict d-closed hull exists in every finite ambient graph. In
an arbitrary graph with growth-bounded finite subgraphs, its cardinality
is uniformly bounded, independently of the chosen finite ambient set.

The finite hull grows monotonically with the ambient set. Select one
whose cardinality is maximal among all finite ambient sets. A strict
d-closure violation in the whole graph would force the finite hull
inside a larger ambient set to grow, contradicting maximality.

This proves the bounded d-closure assertion in Section 2 of
The Big Hrushovski without using a pre-existing countable exhaustion
by d-closed stages, Fraisse genericity or any enumerated presentation.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Finite strict hulls increase as the containing ambient finite set
increases. The essential step is the restriction of a strictly closed
set to an arbitrary smaller finite ambient set by intersection. -/
theorem dClosedHull_mono_ambient
    (d : Predimension V)
    {s c u : Finset V}
    (hsc : s ⊆ c) (hcu : c ⊆ u) :
    d.dClosedHull s c ⊆ d.dClosedHull s u := by
  have hLarge : d.IsDClosed (d.dClosedHull s u) u :=
    d.dClosedHull_dclosed s u
  have hCut : d.IsDClosed ((d.dClosedHull s u) ∩ c) c :=
    d.dclosed_inter_restrict hLarge hcu
  have hsCut : s ⊆ (d.dClosedHull s u) ∩ c := by
    intro x hx
    exact Finset.mem_inter.mpr
      ⟨d.subset_dClosedHull (hsc.trans hcu) hx, hsc hx⟩
  exact (d.dClosedHull_least hsCut hCut).trans Finset.inter_subset_left

/-- A uniform finite cardinality bound on all *finite-ambient* strict
hulls produces a least globally strictly d-closed finite hull.

No chain of globally closed stages is assumed. The proof maximizes
the size of the finite hull among arbitrary finite ambient supersets
of s, and then shows that any global closure violation would increase
that maximal size. -/
theorem exists_least_globalDClosed_hull_of_boundedFiniteHulls
    (d : Predimension V) (s : Finset V) (K : ℕ)
    (hBound : ∀ c : Finset V, s ⊆ c →
      (d.dClosedHull s c).card < K) :
    ∃ h : Finset V,
      s ⊆ h ∧ d.IsGloballyDClosed h ∧ h.card < K ∧
      ∀ t : Finset V, s ⊆ t →
        d.IsGloballyDClosed t → h ⊆ t := by
  classical
  let sizes : Finset ℕ :=
    (Finset.range K).filter (fun n =>
      ∃ c : Finset V, s ⊆ c ∧ (d.dClosedHull s c).card = n)
  have hMem (c : Finset V) (hsc : s ⊆ c) :
      (d.dClosedHull s c).card ∈ sizes := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (hBound c hsc), ⟨c, hsc, rfl⟩⟩
  have hNonempty : sizes.Nonempty :=
    ⟨(d.dClosedHull s s).card, hMem s Finset.Subset.rfl⟩
  have hMaxMem : sizes.max' hNonempty ∈ sizes :=
    Finset.max'_mem sizes hNonempty
  obtain ⟨c, hsc, hcCard⟩ := (Finset.mem_filter.mp hMaxMem).2
  let h : Finset V := d.dClosedHull s c
  have hMax : ∀ u : Finset V, s ⊆ u →
      (d.dClosedHull s u).card ≤ h.card := by
    intro u hsu
    have hLe : (d.dClosedHull s u).card ≤ sizes.max' hNonempty :=
      Finset.le_max' sizes _ (hMem u hsu)
    dsimp [h]
    omega
  have hsH : s ⊆ h := d.subset_dClosedHull hsc
  have hGlobal : d.IsGloballyDClosed h := by
    intro t hht hne
    by_contra hBad
    have hDeltaLe : d.delta t ≤ d.delta h := le_of_not_gt hBad
    let u : Finset V := c ∪ t
    have hsu : s ⊆ u := hsc.trans Finset.subset_union_left
    have hcu : c ⊆ u := Finset.subset_union_left
    have hOld : h ⊆ d.dClosedHull s u :=
      d.dClosedHull_mono_ambient hsc hcu
    have hStrict : h ≠ d.dClosedHull s u := by
      intro hEq
      have hClosedU : d.IsDClosed h u := by
        simpa only [hEq] using d.dClosedHull_dclosed s u
      have hDeltaT : d.delta h < d.delta t :=
        hClosedU.2 t hht hne Finset.subset_union_right
      omega
    have hProper : h ⊂ d.dClosedHull s u :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hOld, hStrict⟩
    have hCardLt : h.card < (d.dClosedHull s u).card :=
      Finset.card_lt_card hProper
    have hCardLe := hMax u hsu
    omega
  have hSize : h.card < K := hBound c hsc
  refine ⟨h, hsH, hGlobal, hSize, ?_⟩
  intro t hst htGlobal
  have hTClosed : d.IsDClosed t (t ∪ c) :=
    IsGloballyDClosed.restrict d htGlobal Finset.subset_union_left
  have hTcap : d.IsDClosed (t ∩ c) c :=
    d.dclosed_inter_restrict hTClosed Finset.subset_union_right
  have hsCap : s ⊆ t ∩ c := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hst hx, hsc hx⟩
  exact (d.dClosedHull_least hsCap hTcap).trans Finset.inter_subset_left

end Predimension

namespace CFGrowthNumerics

/-- The greatest integer at which a monotone unbounded growth function
is at most t, provided F(0) ≤ t. Flat portions are allowed. -/
noncomputable def growthInverseAt
    (F : ℕ → ℝ)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (t : ℝ) : ℕ :=
  Nat.find (hUnbounded t) - 1

theorem growthInverseAt_iff
    (F : ℕ → ℝ) (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    F n ≤ t ↔ n ≤ growthInverseAt F hUnbounded t := by
  have hPos : 0 < Nat.find (hUnbounded t) := by
    by_contra hn
    have heq : Nat.find (hUnbounded t) = 0 := by omega
    have hAbove := Nat.find_spec (hUnbounded t)
    rw [heq, hZero] at hAbove
    linarith
  constructor
  · intro hFn
    have hLt : n < Nat.find (hUnbounded t) := by
      by_contra hn
      have hCut : Nat.find (hUnbounded t) ≤ n := by omega
      have hMonoN : F (Nat.find (hUnbounded t)) ≤ F n :=
        hMono hCut
      have hAbove := Nat.find_spec (hUnbounded t)
      linarith
    dsimp [growthInverseAt]
    omega
  · intro hn
    have hLt : n < Nat.find (hUnbounded t) := by
      dsimp [growthInverseAt] at hn
      omega
    by_contra hBad
    have hAbove : t < F n := lt_of_not_ge hBad
    have hFirst : Nat.find (hUnbounded t) ≤ n :=
      Nat.find_min' (hUnbounded t) hAbove
    omega

end CFGrowthNumerics

namespace GraphOn

variable {V : Type*} [DecidableEq V]

/-- A finite strict hull is bounded independently of the containing
finite ambient graph, using only the growth inequalities on finite
induced vertex sets. -/
theorem growth_dClosedHull_card_lt_cutoff
    (G : GraphOn V) (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (hAge : ∀ u : Finset V, F u.card ≤ (G.predim u : ℝ))
    (s c : Finset V) (hsc : s ⊆ c) :
    (G.toPredimension.dClosedHull s c).card <
      Nat.find (hUnbounded (2 * (s.card : ℝ))) := by
  have hGrowthC : G.IsGrowthSparse F c := by
    intro u _
    exact hAge u
  have hF := G.growth_dClosedHull_le_twice_card F s c hsc hGrowthC
  by_contra hNot
  have hCut : Nat.find (hUnbounded (2 * (s.card : ℝ))) ≤
      (G.toPredimension.dClosedHull s c).card := by omega
  have hMonoN := hMono hCut
  have hAbove := Nat.find_spec (hUnbounded (2 * (s.card : ℝ)))
  linarith

/-- Bounded global d-closure in every graph whose entire finite age
belongs to C_F. Neither countability nor an existing d-closed
exhaustion is assumed. The bound is the exact generalized inverse
at 2|s|, not the larger inverse used for one-point local extensions. -/
theorem exists_least_bounded_globalDClosed_hull
    (G : GraphOn V) (F : ℕ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ n : ℕ, t < F n)
    (hAge : ∀ u : Finset V, F u.card ≤ (G.predim u : ℝ))
    (s : Finset V) :
    ∃ h : Finset V,
      s ⊆ h ∧
      G.toPredimension.IsGloballyDClosed h ∧
      h.card ≤ CFGrowthNumerics.growthInverseAt F hUnbounded
        (2 * (s.card : ℝ)) ∧
      ∀ t : Finset V, s ⊆ t →
        G.toPredimension.IsGloballyDClosed t → h ⊆ t := by
  let K : ℕ := Nat.find (hUnbounded (2 * (s.card : ℝ)))
  have hBound : ∀ c : Finset V, s ⊆ c →
      (G.toPredimension.dClosedHull s c).card < K := by
    intro c hsc
    exact G.growth_dClosedHull_card_lt_cutoff F
      hMono hUnbounded hAge s c hsc
  obtain ⟨h, hs, hGlobal, hCard, hLeast⟩ :=
    G.toPredimension.exists_least_globalDClosed_hull_of_boundedFiniteHulls
      s K hBound
  refine ⟨h, hs, hGlobal, ?_, hLeast⟩
  dsimp [CFGrowthNumerics.growthInverseAt, K]
  omega

end GraphOn
end BigHrushovski
