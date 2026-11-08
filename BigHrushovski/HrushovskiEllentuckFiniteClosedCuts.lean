import BigHrushovski.HrushovskiEllentuckFiniteEnvelopes

/-!
# Finite strictly closed cuts of complete-support C_F domains

For the countable birth-labelled C_F presentation, U[S] consists of
vertices whose *whole finite generated b-closure* has birth levels
in S. The intersection of U[S] with an original finite birth stage
is represented here by a literal Finset of original birth vertices.

It is closed under every complete b-value, hence globally strictly
d-closed by the already verified birth-block closure theorem.
For finite S, the whole supported domain U[S] is such a finite
globally closed vertex set, without invoking unique finite level lifts.

The stronger assertion that its *ordered functional induced structure*
is the canonical finite level presentation is not claimed here.
-/

namespace BigHrushovski.CFCoherentTower

/-- The literal finite cut of U[S] inside the original stage U_n. -/
noncomputable def birthLevelCut (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (n : ℕ) : Finset (Vertex F K) := by
  classical
  exact (stageImage F K n).filter
    (fun v => v ∈ birthLevelDomain F K S)

theorem mem_birthLevelCut_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (n : ℕ) (v : Vertex F K) :
    v ∈ birthLevelCut F K S n ↔
      v ∈ birthLevelDomain F K S ∧
        v ∈ stageImage F K n := by
  classical
  simp [birthLevelCut, and_comm]

/-- Any finite stage cut of a complete-support domain contains
every complete auxiliary b-value of each of its vertices. -/
theorem birthLevelCut_bClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (n : ℕ) :
    IsBirthBlockClosed F K (birthLevelCut F K S n) := by
  apply (birthBlockClosed_iff_bValue_subset F K
    (birthLevelCut F K S n)).mpr
  intro v hv w hw
  obtain ⟨hvS, hvStage⟩ :=
    (mem_birthLevelCut_iff F K S n v).mp hv
  apply (mem_birthLevelCut_iff F K S n w).mpr
  constructor
  · exact birthLevelDomain_bValueClosed F K S hvS hw
  · exact (birthBValue_subset_of_closed F K
      (stageImage F K n)
      (stageImage_birthBlockClosed F K n) hvStage) hw

/-- Every literal finite supported-domain cut is globally strictly
d-closed in the original countable C_F birth graph. -/
theorem birthLevelCut_globalDClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (n : ℕ) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      (birthLevelCut F K S n) :=
  birthBlockClosed_global_dClosed F K
    (birthLevelCut F K S n) (birthLevelCut_bClosed F K S n)

/-- For a *finite* selected level set, the whole domain U[S] has a
literal finite representative that is b-closed and globally strictly
d-closed in the original countable graph. This strengthens mere
finiteness without assuming a functional finite lifting theorem. -/
theorem birthLevelDomain_finset_exists_globalDClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ) (s : Finset ℕ) :
    ∃ t : Finset (Vertex F K),
      (∀ v, v ∈ t ↔
        v ∈ birthLevelDomain F K (↑s : Set ℕ)) ∧
      IsBirthBlockClosed F K t ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed t := by
  obtain ⟨n, hsubset⟩ := birthLevelDomain_finset_subset_stage F K s
  let t := birthLevelCut F K (↑s : Set ℕ) n
  refine ⟨t, ?_, birthLevelCut_bClosed F K _ n,
    birthLevelCut_globalDClosed F K _ n⟩
  intro v
  constructor
  · intro hv
    exact ((mem_birthLevelCut_iff F K (↑s : Set ℕ) n v).mp hv).1
  · intro hv
    exact (mem_birthLevelCut_iff F K (↑s : Set ℕ) n v).mpr
      ⟨hv, hsubset hv⟩

end BigHrushovski.CFCoherentTower
