import BigHrushovski.HrushovskiEllentuckCFBirthTopology

/-!
# Finite supported level envelopes in the actual C_F birth tower

Section 6b uses the finite set U[S] of vertices whose *complete*
generated b-support lies in a prescribed finite set S of birth
levels. The claim of finiteness follows from the exact initial-stage
equality, without selecting or lifting any functional embedding.

The induced structure of U[S] is not asserted to be the canonical
finite level presentation; identifying its exact function values
and its universal property is the independent finite lifting problem.
-/

namespace BigHrushovski.CFCoherentTower

/-- A finite set of natural-number birth levels has a finite upper
cutoff. This is merely the arithmetic input to the structural result. -/
private theorem finiteLevels_bounded (s : Finset ℕ) :
    ∃ n : ℕ, (↑s : Set ℕ) ⊆ Set.Iio n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert a s ha ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨max (a + 1) n, ?_⟩
      intro q hq
      change q < max (a + 1) n
      rcases Finset.mem_insert.mp hq with hqa | hqs
      · subst q
        exact (Nat.lt_succ_self a).trans_le (le_max_left ..)
      · have hqn : q ∈ Set.Iio n := hn hqs
        change q < n at hqn
        exact hqn.trans_le (le_max_right ..)

/-- A complete-support domain on finitely many selected levels is
contained in a *literal* finite birth stage, not an arbitrary copy. -/
theorem birthLevelDomain_finset_subset_stage
    (F : ℕ → ℝ) (K : ℕ → ℕ) (s : Finset ℕ) :
    ∃ n : ℕ,
      birthLevelDomain F K (↑s : Set ℕ) ⊆
        (↑(stageImage F K n) : Set (Vertex F K)) := by
  obtain ⟨n, hn⟩ := finiteLevels_bounded s
  exact ⟨n, birthLevelDomain_subset_stageImage_of_bounded F K hn⟩

/-- The manuscript's concrete finite-level envelope is finite as
a vertex set. No finite inverse assignment or countable level lift
is used in this proof. -/
theorem birthLevelDomain_finset_finite
    (F : ℕ → ℝ) (K : ℕ → ℕ) (s : Finset ℕ) :
    (birthLevelDomain F K (↑s : Set ℕ)).Finite := by
  obtain ⟨n, hn⟩ := birthLevelDomain_finset_subset_stage F K s
  exact (Finset.finite_toSet (stageImage F K n)).subset hn

end BigHrushovski.CFCoherentTower
