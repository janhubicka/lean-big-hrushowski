import BigHrushovski.HrushovskiEllentuckFiniteClosedCuts
import BigHrushovski.HrushovskiEllentuckStageCuts

/-!
# Strictly d-closed finite exhaustion of supported C_F domains

For the actual countable C_F birth graph, the full-support domain U[S]
of an arbitrary set of birth levels is the increasing union of its
literal finite birth-stage cuts.

Each cut is closed under all complete auxiliary b-values and globally
strictly d-closed in the countable graph. Every finite subset of U[S]
is contained in one such cut, with *no* canonical finite-level lift
or assumption on the gaps in S.

The exhaustion here uses ambient birth-stage cutoffs, not the first n
represented levels of a copy. In particular the proof does not identify
U[S] with the range of a self-embedding in the final (R,H) language.
-/

namespace BigHrushovski.CFCoherentTower

/-- Literal supported-domain cuts increase with their birth-stage
cutoff. No Ramsey-space approximation ordering is involved. -/
theorem birthLevelCut_mono
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ)
    {n m : ℕ} (hnm : n ≤ m) :
    birthLevelCut F K S n ⊆ birthLevelCut F K S m := by
  intro v hv
  obtain ⟨hvS, hvStage⟩ :=
    (mem_birthLevelCut_iff F K S n v).mp hv
  exact (mem_birthLevelCut_iff F K S m v).mpr
    ⟨hvS, stageImage_mono F K hnm hvStage⟩

/-- Every supported vertex belongs to one literal finite cut, and
all these cuts lie inside the supported domain. -/
theorem birthLevelDomain_eq_iUnion_birthLevelCuts
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) :
    birthLevelDomain F K S =
      ⋃ n : ℕ, (↑(birthLevelCut F K S n) : Set (Vertex F K)) := by
  ext v
  constructor
  · intro hv
    apply Set.mem_iUnion.mpr
    refine ⟨v.1 + 1, ?_⟩
    change v ∈ birthLevelCut F K S (v.1 + 1)
    exact (mem_birthLevelCut_iff F K S (v.1 + 1) v).mpr
      ⟨hv, (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).mpr
        (Nat.lt_succ_self v.1)⟩
  · intro hv
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    change v ∈ birthLevelCut F K S n at hn
    exact ((mem_birthLevelCut_iff F K S n v).mp hn).1

/-- A single literal finite, globally strictly d-closed cut contains
any specified finite set of vertices from a supported domain. -/
theorem finite_supported_vertices_in_closedCut
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (s : Finset (Vertex F K))
    (hs : ∀ v ∈ s, v ∈ birthLevelDomain F K S) :
    ∃ n : ℕ, s ⊆ birthLevelCut F K S n := by
  obtain ⟨n, hn⟩ := finiteSet_covered F K s
  refine ⟨n, ?_⟩
  intro v hv
  exact (mem_birthLevelCut_iff F K S n v).mpr ⟨hs v hv, hn hv⟩

/-- The exact exhaustion package for complete b-support domains.
The complete finite b-values and the global *strict* d-closure hold
at every stage, while the stage family is increasing and covers
precisely U[S]. This does not identify the final functional copy
space with the supported-domain space. -/
theorem birthLevelDomain_strictClosedExhaustion
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) :
    (∀ n, IsBirthBlockClosed F K (birthLevelCut F K S n)) ∧
    (∀ n, (countableGraph F K).toPredimension.IsGloballyDClosed
      (birthLevelCut F K S n)) ∧
    (∀ n, birthLevelCut F K S n ⊆ birthLevelCut F K S (n+1)) ∧
    birthLevelDomain F K S =
      ⋃ n : ℕ, (↑(birthLevelCut F K S n) : Set (Vertex F K)) := by
  refine ⟨birthLevelCut_bClosed F K S,
    birthLevelCut_globalDClosed F K S, ?_,
    birthLevelDomain_eq_iUnion_birthLevelCuts F K S⟩
  intro n
  exact birthLevelCut_mono F K S (Nat.le_succ n)

end BigHrushovski.CFCoherentTower
