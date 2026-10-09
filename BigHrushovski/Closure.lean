import BigHrushovski.Predimension

/-!
Finite strong hulls within a fixed finite ambient graph. The separate
countable-limit finite-container assertion is not established here.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Intersection of finitely many sets, inside finite ambient c. -/
noncomputable def intersectFamily
    (c : Finset V) (fs : Finset (Finset V)) : Finset V := by
  classical
  exact c.filter (fun v => ∀ b ∈ fs, v ∈ b)

theorem intersectFamily_empty (c : Finset V) :
    intersectFamily c ∅ = c := by
  classical
  ext v
  simp [intersectFamily]

theorem intersectFamily_insert (c b : Finset V) (fs : Finset (Finset V)) :
    intersectFamily c (insert b fs) = intersectFamily c fs ∩ b := by
  classical
  ext v
  simp only [intersectFamily, Finset.mem_filter, Finset.mem_inter]
  constructor
  · intro h
    refine ⟨⟨h.1, ?_⟩, ?_⟩
    · intro t ht
      exact h.2 t (Finset.mem_insert_of_mem ht)
    · exact h.2 b (Finset.mem_insert_self b fs)
  · rintro ⟨⟨hc, hrest⟩, hb⟩
    refine ⟨hc, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with htb | htfs
    · subst t
      exact hb
    · exact hrest t htfs

/-- Finite intersections of strong substructures are strong. -/
theorem strong_intersectFamily (d : Predimension V) (c : Finset V)
    (fs : Finset (Finset V))
    (hfs : ∀ b ∈ fs, d.IsStrong b c) :
    d.IsStrong (intersectFamily c fs) c := by
  classical
  induction fs using Finset.induction_on with
  | empty =>
      simpa [intersectFamily_empty] using d.strong_refl c
  | @insert b fs hnot ih =>
      have hb : d.IsStrong b c := hfs b (Finset.mem_insert_self b fs)
      have hrest : ∀ t ∈ fs, d.IsStrong t c := by
        intro t ht
        exact hfs t (Finset.mem_insert_of_mem ht)
      rw [intersectFamily_insert]
      exact d.strong_inter (ih hrest) hb

/-- Least strong subset of a finite ambient set containing a. -/
noncomputable def strongHull (d : Predimension V)
    (a c : Finset V) : Finset V := by
  classical
  exact intersectFamily c
    (c.powerset.filter (fun b => a ⊆ b ∧ d.IsStrong b c))

theorem strongHull_strong (d : Predimension V) (a c : Finset V) :
    d.IsStrong (d.strongHull a c) c := by
  classical
  unfold strongHull
  apply d.strong_intersectFamily
  intro b hb
  exact (Finset.mem_filter.mp hb).2.2

theorem subset_strongHull (d : Predimension V) {a c : Finset V}
    (hac : a ⊆ c) : a ⊆ d.strongHull a c := by
  classical
  intro v hv
  change v ∈ intersectFamily c
    (c.powerset.filter (fun b => a ⊆ b ∧ d.IsStrong b c))
  apply Finset.mem_filter.mpr
  refine ⟨hac hv, ?_⟩
  intro b hb
  exact (Finset.mem_filter.mp hb).2.1 hv

theorem strongHull_least (d : Predimension V) {a b c : Finset V}
    (hab : a ⊆ b) (hbc : d.IsStrong b c) :
    d.strongHull a c ⊆ b := by
  classical
  intro v hv
  have hmem : b ∈ c.powerset.filter (fun t => a ⊆ t ∧ d.IsStrong t c) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hbc.1, ⟨hab, hbc⟩⟩
  exact (Finset.mem_filter.mp hv).2 b hmem

theorem exists_least_strong_hull (d : Predimension V)
    {a c : Finset V} (hac : a ⊆ c) :
    ∃ h : Finset V, a ⊆ h ∧ d.IsStrong h c ∧
      ∀ b : Finset V, a ⊆ b → d.IsStrong b c → h ⊆ b := by
  exact ⟨d.strongHull a c, d.subset_strongHull hac,
    d.strongHull_strong a c, fun b hab hbc => d.strongHull_least hab hbc⟩

end Predimension
end BigHrushovski
