import BigHrushovski.HrushovskiEllentuckFiniteClosedCuts
import BigHrushovski.HrushovskiEllentuckFinitaryContinuity

/-!
# Finite-character completion of complete-support domains

A complete-support domain is determined by a set of levels, but an
arbitrary set of vertices need not be a support domain. Its least
support domain is obtained by retaining all levels appearing in the
complete supports of its vertices.

The resulting completion has finite character: whenever a vertex
belongs to the completion of an arbitrary set, finitely many
vertices already witness this. This is an exact finitary closure
condition for the family of support domains, not a Ramsey theorem
or a claim that such domains are ranges of functional embeddings.

For the actual countable C_F birth presentation, the completion
of a *finite* vertex set is again finite, and it has a literal
representative closed under all b-values and globally strictly
d-closed. This gives a canonical finite enlargement among
complete-support domains, without choosing finite level lifts.
-/

namespace BigHrushovski.Ellentuck

universe u v
variable {Vertex : Type u} {Level : Type v}

/-- All levels represented in the complete supports of vertices of X. -/
def supportLevels (support : Vertex → Finset Level)
    (X : Set Vertex) : Set Level :=
  {q | ∃ x ∈ X, q ∈ support x}

/-- Least support-saturated vertex set containing X. -/
def supportCompletion (support : Vertex → Finset Level)
    (X : Set Vertex) : Set Vertex :=
  supportDomain support (supportLevels support X)

/-- Every vertex belongs to the domain obtained from its own levels. -/
theorem subset_supportCompletion
    (support : Vertex → Finset Level) (X : Set Vertex) :
    X ⊆ supportCompletion support X := by
  intro v hv q hq
  exact ⟨v, hv, hq⟩

/-- Completion is the smallest support domain containing X. -/
theorem supportCompletion_least
    (support : Vertex → Finset Level) (X : Set Vertex)
    (S : Set Level)
    (hXS : X ⊆ supportDomain support S) :
    supportCompletion support X ⊆ supportDomain support S := by
  intro v hv q hq
  obtain ⟨x, hx, hxq⟩ := hv q hq
  exact hXS hx q hxq

theorem supportCompletion_mono
    (support : Vertex → Finset Level) {X Y : Set Vertex}
    (hXY : X ⊆ Y) :
    supportCompletion support X ⊆ supportCompletion support Y := by
  intro v hv q hq
  obtain ⟨x, hx, hxq⟩ := hv q hq
  exact ⟨x, hXY hx, hxq⟩

/-- Taking the represented levels again introduces no new levels. -/
theorem supportLevels_completion
    (support : Vertex → Finset Level) (X : Set Vertex) :
    supportLevels support (supportCompletion support X) =
      supportLevels support X := by
  apply Set.Subset.antisymm
  · rintro q ⟨v, hv, hq⟩
    exact hv q hq
  · rintro q ⟨v, hv, hq⟩
    exact ⟨v, subset_supportCompletion support X hv, hq⟩

theorem supportCompletion_idempotent
    (support : Vertex → Finset Level) (X : Set Vertex) :
    supportCompletion support (supportCompletion support X) =
      supportCompletion support X := by
  change supportDomain support
      (supportLevels support (supportCompletion support X)) =
    supportDomain support (supportLevels support X)
  rw [supportLevels_completion]

/-- Every support domain is already complete, even if some levels are
not represented by a singleton-support vertex. -/
theorem supportCompletion_of_domain
    (support : Vertex → Finset Level) (S : Set Level) :
    supportCompletion support (supportDomain support S) =
      supportDomain support S := by
  apply Set.Subset.antisymm
  · exact supportCompletion_least support _ S (Set.Subset.rfl)
  · exact subset_supportCompletion support _

/-- Finite character: only finitely many existing vertices of X are
needed to witness that all levels of a particular vertex are present.
This uses finiteness of the *full* support, not of the vertex set X. -/
theorem mem_supportCompletion_iff_finite_witness
    (support : Vertex → Finset Level) (X : Set Vertex) (v : Vertex) :
    v ∈ supportCompletion support X ↔
      ∃ s : Finset Vertex, (↑s : Set Vertex) ⊆ X ∧
        v ∈ supportCompletion support (↑s : Set Vertex) := by
  classical
  constructor
  · intro hv
    have hChosen :
        ∀ q : {p : Level // p ∈ support v},
          ∃ w : Vertex, w ∈ X ∧ q.1 ∈ support w := by
      intro q
      exact hv q.1 q.2
    let w : {p : Level // p ∈ support v} → Vertex :=
      fun q => Classical.choose (hChosen q)
    have hw : ∀ q, w q ∈ X ∧ q.1 ∈ support (w q) := by
      intro q
      exact Classical.choose_spec (hChosen q)
    refine ⟨(support v).attach.image w, ?_, ?_⟩
    · intro x hx
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hw q).1
    · intro q hq
      refine ⟨w ⟨q, hq⟩, ?_, (hw ⟨q, hq⟩).2⟩
      exact Finset.mem_image.mpr
        ⟨⟨q, hq⟩, by simp, rfl⟩
  · rintro ⟨s, hs, hv⟩
    exact supportCompletion_mono support hs hv

/-- A vertex set is a complete-support domain exactly when it is
closed under finite support-completion tests. This is a finitary
criterion, not a replacement for concrete Ramsey-space axioms. -/
theorem supportCompletion_fixed_iff_finite_tests
    (support : Vertex → Finset Level) (X : Set Vertex) :
    supportCompletion support X = X ↔
      ∀ s : Finset Vertex, (↑s : Set Vertex) ⊆ X →
        supportCompletion support (↑s : Set Vertex) ⊆ X := by
  constructor
  · intro hX s hs
    rw [← hX]
    exact supportCompletion_mono support hs
  · intro hFinite
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨s, hs, hvs⟩ :=
        (mem_supportCompletion_iff_finite_witness support X v).mp hv
      exact hFinite s hs hvs
    · exact subset_supportCompletion support X

end BigHrushovski.Ellentuck

namespace BigHrushovski.CFCoherentTower

/-- Finite union of the *complete generated* level supports of s. -/
noncomputable def finiteBirthSupportLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Finset ℕ := by
  classical
  exact s.biUnion (birthLevelSupport F K)

/-- Canonical finite-support enlargement of an arbitrary finite
vertex set in the actual countable C_F presentation. -/
def finiteBirthSupportCompletion
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Set (Vertex F K) :=
  birthLevelDomain F K (↑(finiteBirthSupportLevels F K s) : Set ℕ)

/-- Every original vertex is retained with its full b-generated
support, not just with its own birth level. -/
theorem finiteBirthSupportCompletion_contains
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    ∀ v ∈ s, v ∈ finiteBirthSupportCompletion F K s := by
  intro v hv q hq
  change q ∈ finiteBirthSupportLevels F K s
  change q ∈ s.biUnion (birthLevelSupport F K)
  exact Finset.mem_biUnion.mpr ⟨v, hv, hq⟩

/-- Every supported domain containing s also contains this finite
enlargement. No claim of least *d-closed* hull is made. -/
theorem finiteBirthSupportCompletion_least
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (S : Set ℕ)
    (hs : ∀ v ∈ s, v ∈ birthLevelDomain F K S) :
    finiteBirthSupportCompletion F K s ⊆
      birthLevelDomain F K S := by
  intro v hv q hq
  have hqs : q ∈ finiteBirthSupportLevels F K s := hv q hq
  change q ∈ s.biUnion (birthLevelSupport F K) at hqs
  obtain ⟨w, hw, hwq⟩ := Finset.mem_biUnion.mp hqs
  exact hs w hw q hwq

/-- Inclusion of finite vertex sets induces inclusion of their
canonical finite support enlargements. -/
theorem finiteBirthSupportCompletion_mono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    {s t : Finset (Vertex F K)} (hst : s ⊆ t) :
    finiteBirthSupportCompletion F K s ⊆
      finiteBirthSupportCompletion F K t := by
  apply finiteBirthSupportCompletion_least F K s
    (↑(finiteBirthSupportLevels F K t) : Set ℕ)
  intro v hv
  exact finiteBirthSupportCompletion_contains F K t v (hst hv)

/-- The canonical enlargement of any finite set remains finite. -/
theorem finiteBirthSupportCompletion_finite
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    (finiteBirthSupportCompletion F K s).Finite :=
  birthLevelDomain_finset_finite F K (finiteBirthSupportLevels F K s)

/-- A literal finite representative of the enlargement is closed
under all b-values and globally strictly d-closed. This gives an
explicit finite strictly closed superstructure for any finite s. -/
theorem finiteBirthSupportCompletion_exists_globalDClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    ∃ t : Finset (Vertex F K),
      (∀ v, v ∈ t ↔
        v ∈ finiteBirthSupportCompletion F K s) ∧
      s ⊆ t ∧
      IsBirthBlockClosed F K t ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed t := by
  obtain ⟨t, ht, hClosed, hDClosed⟩ :=
    birthLevelDomain_finset_exists_globalDClosed F K
      (finiteBirthSupportLevels F K s)
  refine ⟨t, ?_, ?_, hClosed, hDClosed⟩
  · intro v
    exact ht v
  · intro v hv
    exact (ht v).2 (finiteBirthSupportCompletion_contains F K s v hv)

end BigHrushovski.CFCoherentTower
