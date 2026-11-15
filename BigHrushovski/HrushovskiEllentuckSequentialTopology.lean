import BigHrushovski.HrushovskiEllentuckFiniteCutTopology

/-!
# Sequential comparison of natural level and vertex observations

This elementary result is deliberately independent of the still-stacked
ordered R/H copy-domain transport. It compares eventual agreement on
all finite prefixes of birth levels with eventual agreement on all
actual vertices in each finite birth stage.

The statement uses the whole generated b-support of every vertex.
It does not identify the Ellentuck neighborhood topology, which is
finer than the metric topology; it concerns only the natural
finite-observation (product/metric) topology.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue CFGrowthNumerics

/-- Finite-level coordinate convergence of a sequence of level sets
is equivalent to finite-stage vertex-domain convergence of the
associated full-support domains. This requires a singleton-level
detector at every stage, obtained from an empty-old-support request. -/
theorem birthLevelDomain_sequential_finite_observations_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (S : ℕ → Set ℕ) (T : Set ℕ) :
    (∀ m : ℕ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      ∀ n : ℕ, n < m → (n ∈ S i ↔ n ∈ T)) ↔
    (∀ m : ℕ, ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
      ∀ v : Vertex F K, v ∈ stageImage F K m →
        (v ∈ birthLevelDomain F K (S i) ↔
          v ∈ birthLevelDomain F K T)) := by
  constructor
  · intro h m
    obtain ⟨N, hN⟩ := h m
    refine ⟨N, ?_⟩
    intro i hi
    exact (birthLevelDomain_agree_on_stage_iff
      F K hReq (S i) T m).mp (hN i hi)
  · intro h m
    obtain ⟨N, hN⟩ := h m
    refine ⟨N, ?_⟩
    intro i hi
    exact (birthLevelDomain_agree_on_stage_iff
      F K hReq (S i) T m).mpr (hN i hi)

end BigHrushovski.CFCoherentTower
