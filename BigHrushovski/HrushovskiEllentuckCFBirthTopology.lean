import BigHrushovski.HrushovskiEllentuckCFBirthSupport

/-!
# Finite coordinates of complete-support domains in the countable C_F tower

The natural product topology on copy domains is controlled coordinatewise:
whether v belongs to the saturated domain U[S] depends only on the
finitely many level coordinates in its *complete* generated support.
All these coordinates are at most the original birth level of v.

These proofs are about actual countable birth-labelled vertices and
their complete generated b-closures. They do not identify U[S] with
the image of an arbitrary functional self-embedding; that remains the
unique level-lifting and range-recognition obligation of Track B.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- All levels represented in the complete generated closure of v
are at most the birth level of v. This uses the exact b-closedness of
the original finite birth stage U_(birth(v)+1). -/
theorem birthLevelSupport_le_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K)
    {q : ℕ} (hq : q ∈ birthLevelSupport F K v) :
    q ≤ v.1 := by
  have hvStage : v ∈ stageImage F K (v.1 + 1) :=
    (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).2
      (Nat.lt_succ_self v.1)
  have hClosureStage :
      birthSingletonClosure F K v ⊆ stageImage F K (v.1 + 1) :=
    birthGeneratedClosure_le_of_closed F K
      ({v} : Finset (Vertex F K))
      (stageImage F K (v.1 + 1))
      (by simpa using hvStage)
      (stageImage_birthBlockClosed F K (v.1 + 1))
  obtain ⟨w, hw, hwq⟩ :=
    (birthLevelSupport_mem_iff F K v q).1 hq
  have hwLt : w.1 < v.1 + 1 :=
    (mem_stageImage_iff_birth_lt F K (v.1 + 1) w).1
      (hClosureStage hw)
  have hwLe : w.1 ≤ v.1 := Nat.le_of_lt_succ hwLt
  exact hwq ▸ hwLe

/-- Membership of v in U[S] depends only on the finite list of levels
in its complete generated closure. -/
theorem birthLevelDomain_local
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S T : Set ℕ) (v : Vertex F K)
    (hST : ∀ q ∈ birthLevelSupport F K v, (q ∈ S ↔ q ∈ T)) :
    v ∈ birthLevelDomain F K S ↔ v ∈ birthLevelDomain F K T :=
  Ellentuck.supportDomain_local (birthLevelSupport F K) S T v hST

/-- In particular level subsets with the same coordinates through
the birth of v cannot be distinguished by membership of v. -/
theorem birthLevelDomain_local_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S T : Set ℕ) (v : Vertex F K)
    (hST : ∀ q ≤ v.1, (q ∈ S ↔ q ∈ T)) :
    v ∈ birthLevelDomain F K S ↔ v ∈ birthLevelDomain F K T := by
  apply birthLevelDomain_local F K S T v
  intro q hq
  exact hST q (birthLevelSupport_le_birth F K v hq)

/-- Supported domains preserve arbitrary binary intersections of
level sets. The analogous union equality is false in general. -/
theorem birthLevelDomain_inter
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S T : Set ℕ) :
    birthLevelDomain F K (S ∩ T) =
      birthLevelDomain F K S ∩ birthLevelDomain F K T :=
  Ellentuck.supportDomain_inter (birthLevelSupport F K) S T

/-- Enlarging the retained level set only enlarges its domain. -/
theorem birthLevelDomain_mono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    {S T : Set ℕ} (hST : S ⊆ T) :
    birthLevelDomain F K S ⊆ birthLevelDomain F K T :=
  Ellentuck.supportDomain_mono (birthLevelSupport F K) hST

/-- Every vertex in a complete-support domain already belongs to the
supported subdomain on a finite set of the selected levels. -/
theorem birthLevelDomain_mem_finite_witness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (S : Set ℕ) (v : Vertex F K) :
    v ∈ birthLevelDomain F K S ↔
      ∃ T : Finset ℕ, (↑T : Set ℕ) ⊆ S ∧
        v ∈ birthLevelDomain F K (↑T : Set ℕ) :=
  Ellentuck.mem_supportDomain_iff_finite_witness
    (birthLevelSupport F K) S v

/-- Any level set bounded by n gives a vertex domain inside the
literal stage U_n. No copy-range or unique lifting assertion is
used in this boundedness statement. -/
theorem birthLevelDomain_subset_stageImage_of_bounded
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    {S : Set ℕ} {n : ℕ} (hS : S ⊆ Set.Iio n) :
    birthLevelDomain F K S ⊆
      (↑(stageImage F K n) : Set (Vertex F K)) := by
  have hmono : birthLevelDomain F K S ⊆
      birthLevelDomain F K (Set.Iio n) :=
    birthLevelDomain_mono F K hS
  rw [← birthLevelDomain_initial_eq_stageImage F K n]
  exact hmono

end CFCoherentTower
end BigHrushovski
