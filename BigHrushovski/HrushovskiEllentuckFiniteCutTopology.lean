import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness

/-!
# Finite-cut comparison of level and vertex-domain observations

Let U[S] be the subset of the *actual* countable C_F birth carrier
consisting of vertices whose complete generated b-support has all
its birth levels in S.

For every finite birth stage U_m, two supported domains have the same
membership answers at every vertex of U_m if and only if their level
sets have the same membership answers at all levels n < m.

The forward implication is finite-character locality: all levels in
the complete generated b-support of a vertex lie at or before its
birth. The converse uses an actual empty-old-support birth request
at each level to detect that level with a singleton-*level*
support witness. No assumption that the fresh birth block has
one vertex is made.

This is the exact finite-coordinate comparison needed for the
natural product topology. It is independent of the still-stacked
actual R/H copy-domain and Ramsey-space equivalences. The
topological-space equality itself is not claimed in this module.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue CFGrowthNumerics

/-- Agreement on the first m birth-level coordinates is equivalent
to agreement on *all actual vertices* of the original finite
birth stage U_m, tested in the complete-support domains U[S], U[T].
The result holds for arbitrary level sets S,T, not just images
of strictly increasing enumerations. -/
theorem birthLevelDomain_agree_on_stage_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (S T : Set ℕ) (m : ℕ) :
    (∀ n : ℕ, n < m → (n ∈ S ↔ n ∈ T)) ↔
      (∀ v : Vertex F K, v ∈ stageImage F K m →
        (v ∈ birthLevelDomain F K S ↔
          v ∈ birthLevelDomain F K T)) := by
  constructor
  · intro hST v hv
    exact birthLevelDomain_local_birth F K S T v (by
      intro q hq
      exact hST q (lt_of_le_of_lt hq
        ((mem_stageImage_iff_birth_lt F K m v).mp hv)))
  · intro hDomain n hn
    obtain ⟨r, hr⟩ := hReq n
    let z : Vertex F K := birthRoot F K n r
    have hzStage : z ∈ stageImage F K m := by
      apply (mem_stageImage_iff_birth_lt F K m z).mpr
      change n < m
      exact hn
    have hSupport : birthLevelSupport F K z = {n} :=
      birthLevelSupport_root_empty_request F K n r hr
    have hMem (U : Set ℕ) :
        z ∈ birthLevelDomain F K U ↔ n ∈ U := by
      change (∀ q ∈ birthLevelSupport F K z, q ∈ U) ↔ n ∈ U
      rw [hSupport]
      simp
    exact (hMem S).symm.trans ((hDomain z hzStage).trans (hMem T))


/-- The first m levels of a strictly increasing image select
exactly those vertices of the *full* complete-support domain
whose birth level belongs to that image prefix. This is an
equality of literal vertex sets and requires no embedding-lift,
empty-request hypothesis, or Ramsey-space instance. -/
theorem birthLevelDomain_increasing_prefix
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h) (m : ℕ) :
    birthLevelDomain F K (Set.image h (Set.Iio m)) =
      {v : Vertex F K |
        v ∈ birthLevelDomain F K (Set.range h) ∧
          v.1 ∈ Set.image h (Set.Iio m)} := by
  ext v
  constructor
  · intro hv
    refine ⟨birthLevelDomain_mono F K ?_ hv,
      hv v.1 (birthLevelSupport_self F K v)⟩
    intro q hq
    obtain ⟨j, hj, rfl⟩ := hq
    exact ⟨j, rfl⟩
  · rintro ⟨hv, ⟨k, hk, hbirth⟩⟩
    intro q hq
    obtain ⟨j, rfl⟩ := hv q hq
    have hle : h j ≤ h k := by
      calc
        h j ≤ v.1 := birthLevelSupport_le_birth F K v hq
        _ = h k := hbirth.symm
    have hjk : j ≤ k := by
      by_contra hnot
      exact (Nat.not_lt_of_ge hle)
        (hh (Nat.lt_of_not_ge hnot))
    exact ⟨j, lt_of_le_of_lt hjk hk, rfl⟩

end BigHrushovski.CFCoherentTower
