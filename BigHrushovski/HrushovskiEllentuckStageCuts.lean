import BigHrushovski.HrushovskiEllentuckFiniteEnvelopes

/-!
# Literal finite stage cuts of complete-support domains in C_F

For a set S of birth levels, write U[S] for the vertices whose
*complete generated b-support* is contained in S. A vertex in the
original stage U_n has all its generated support at levels below n.

Consequently the cut U[S] ∩ U_n agrees exactly with U[S ∩ [0,n)].
Every U[S] is an increasing union of such finite cuts, even for
infinite S. These are the ambient birth-stage cuts, **not** the
abstract Ramsey approximations by the first n represented levels
of a functional embedding range. The latter correspondence still
requires unique finite and countable level lifting.
-/

namespace BigHrushovski.CFCoherentTower

/-- Intersecting a complete-support domain with an original literal
birth stage is the same as restricting allowed support levels to
the corresponding initial interval. No functional lift is involved. -/
theorem birthLevelDomain_inter_stageImage
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) (n : ℕ) :
    birthLevelDomain F K S ∩
        (↑(stageImage F K n) : Set (Vertex F K)) =
      birthLevelDomain F K (S ∩ Set.Iio n) := by
  rw [← birthLevelDomain_initial_eq_stageImage F K n]
  exact (birthLevelDomain_inter F K S (Set.Iio n)).symm

/-- Each ambient birth-stage cut of a supported domain is finite.
This statement does not assert that the cut has the canonical
induced functional presentation for a chosen finite set of levels. -/
theorem birthLevelDomain_inter_stageImage_finite
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) (n : ℕ) :
    (birthLevelDomain F K S ∩
      (↑(stageImage F K n) : Set (Vertex F K))).Finite := by
  exact (Finset.finite_toSet (stageImage F K n)).subset
    Set.inter_subset_right

/-- Every complete-support domain is the increasing union of its
literal finite birth-stage cuts. No empty-level or singleton-level
witness is required. -/
theorem birthLevelDomain_eq_iUnion_stageCuts
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) :
    birthLevelDomain F K S =
      ⋃ n : ℕ, (birthLevelDomain F K S ∩
        (↑(stageImage F K n) : Set (Vertex F K))) := by
  ext v
  constructor
  · intro hv
    apply Set.mem_iUnion.mpr
    refine ⟨v.1 + 1, ?_⟩
    exact ⟨hv, (mem_stageImage_iff_birth_lt F K (v.1 + 1) v).2
      (Nat.lt_succ_self v.1)⟩
  · intro hv
    rcases Set.mem_iUnion.mp hv with ⟨n, hn⟩
    exact hn.1

/-- Equivalently, U[S] is the union of the supported domains over
its initial finite level restrictions. This is a useful algebraic
identity for comparing natural product topologies. -/
theorem birthLevelDomain_eq_iUnion_initialLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ) (S : Set ℕ) :
    birthLevelDomain F K S =
      ⋃ n : ℕ, birthLevelDomain F K (S ∩ Set.Iio n) := by
  calc
    birthLevelDomain F K S =
      ⋃ n : ℕ, (birthLevelDomain F K S ∩
        (↑(stageImage F K n) : Set (Vertex F K))) :=
      birthLevelDomain_eq_iUnion_stageCuts F K S
    _ = ⋃ n : ℕ, birthLevelDomain F K (S ∩ Set.Iio n) := by
      apply Set.iUnion_congr
      intro n
      exact birthLevelDomain_inter_stageImage F K S n

end BigHrushovski.CFCoherentTower
