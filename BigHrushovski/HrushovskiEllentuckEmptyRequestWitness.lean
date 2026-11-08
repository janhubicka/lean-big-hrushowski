import BigHrushovski.HrushovskiEllentuckCFBirthTopology
import BigHrushovski.CFBirthTopBlock
import BigHrushovski.CFSingletonStageCoverage

/-!
# Empty-support requests detect the original birth levels

The exact complete b-generated closure of a fresh vertex in the
tagged C_F birth tower consists of its entire birth block together
with the generated closure of its named old support.

If that old support is empty, the complete closure is precisely
the fresh block. All vertices of the block have the same birth level.
Hence the full finite support of any vertex in such a block is
exactly the singleton containing its birth level, regardless of
whether the block has more than one vertex.

Under an explicit hypothesis that every stage has some empty-support
request, these witnesses recover inclusion of level sets from
inclusion of complete-support domains. The actual existence of
empty-support requests from the published C_F class assumptions is
a separate Track C input.
-/

namespace BigHrushovski.CFCoherentTower

open CFGrowthNumerics CFStageCatalogue

/-- Empty named old support has empty literal image in the
countable birth-labelled carrier. -/
theorem birthSupport_empty_of_empty_request
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n)
    (hr : r.support = ∅) :
    birthSupport F K n r = ∅ := by
  classical
  simp [birthSupport, taggedSupport, hr]

/-- The least finite complete-b-closed hull of the empty vertex set
is empty, with no extra growth or level-lifting assumptions. -/
theorem birthGeneratedClosure_empty
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    birthGeneratedClosure F K
      (∅ : Finset (Vertex F K)) = ∅ := by
  have hEmpty : IsBirthBlockClosed F K
      (∅ : Finset (Vertex F K)) := by
    intro n r i hi
    simp at hi
  have hsub := birthGeneratedClosure_le_of_closed F K
    (∅ : Finset (Vertex F K))
    (∅ : Finset (Vertex F K))
    (by intro v hv; exact hv) hEmpty
  exact Finset.subset_empty.mp hsub

/-- The complete one-generated closure of a first vertex of an
empty-support request is its whole literal birth block. -/
theorem birthSingletonClosure_root_empty_request
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n)
    (hr : r.support = ∅) :
    birthSingletonClosure F K (birthRoot F K n r) =
      birthBlock F K n r := by
  have hDecomp :
      birthSingletonClosure F K (birthRoot F K n r) =
        birthGeneratedClosure F K (birthSupport F K n r) ∪
          birthBlock F K n r :=
    birthGeneratedClosure_fresh_decompose F K n r
      ⟨0, r.code.2.fresh_pos⟩
  rw [birthSupport_empty_of_empty_request F K n r hr,
    birthGeneratedClosure_empty F K] at hDecomp
  simpa only [Finset.empty_union] using hDecomp

/-- Even a multi-vertex block with empty old support provides a
singleton-*level* witness. We do not assume the block is a singleton. -/
theorem birthLevelSupport_root_empty_request
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n)
    (hr : r.support = ∅) :
    birthLevelSupport F K (birthRoot F K n r) = {n} := by
  classical
  have hClosure :=
    birthSingletonClosure_root_empty_request F K n r hr
  ext q
  constructor
  · intro hq
    obtain ⟨w, hw, heq⟩ :=
      (birthLevelSupport_mem_iff F K (birthRoot F K n r) q).mp hq
    rw [hClosure] at hw
    have hBirth := birthBlock_birth_eq F K n r hw
    exact Finset.mem_singleton.mpr (heq.symm.trans hBirth)
  · intro hq
    have hqn : q = n := Finset.mem_singleton.mp hq
    subst q
    exact birthLevelSupport_self F K (birthRoot F K n r)

/-- Under a separate empty-support request at each level,
the actual birth presentation has enough singleton-level
support witnesses for the level-to-domain map. -/
theorem birthLevelSupport_all_singleton_witnesses
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    ∀ n : ℕ, ∃ z : Vertex F K,
      birthLevelSupport F K z = {n} := by
  intro n
  obtain ⟨r, hr⟩ := hReq n
  exact ⟨birthRoot F K n r,
    birthLevelSupport_root_empty_request F K n r hr⟩

/-- Exact order reflection by supported domains, now on the
genuine C_F birth carrier, conditional only on an empty-support
request at each original level. -/
theorem birthLevelDomain_subset_iff_of_empty_requests
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (S T : Set ℕ) :
    birthLevelDomain F K S ⊆ birthLevelDomain F K T ↔
      S ⊆ T := by
  constructor
  · intro hST n hn
    obtain ⟨z, hz⟩ :=
      birthLevelSupport_all_singleton_witnesses F K hReq n
    have hzS : z ∈ birthLevelDomain F K S := by
      intro q hq
      have hqn : q = n := Finset.mem_singleton.mp (hz ▸ hq)
      exact hqn ▸ hn
    have hzT : z ∈ birthLevelDomain F K T := hST hzS
    exact hzT n (by simpa only [hz, Finset.mem_singleton])
  · exact birthLevelDomain_mono F K


/-- The paper's real-growth C_F class assumptions provide a
singleton-support witness on every actual birth level. -/
theorem realBirthLevelSupport_singleton_witnesses
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2) :
    ∀ n : ℕ,
      ∃ z : Vertex (cardinalGrowth F)
        (cardinalGrowthBound F hMono hUnbounded),
        birthLevelSupport (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) z = {n} :=
  birthLevelSupport_all_singleton_witnesses
    (cardinalGrowth F) (cardinalGrowthBound F hMono hUnbounded)
    (singletonEmptySupportRequest_every_realStage
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton)

/-- Under the published C_F class hypotheses, complete support
domains preserve *and reflect* inclusion of level sets. This
does not itself identify these domains with functional copy ranges. -/
theorem realBirthLevelDomain_subset_iff
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2)
    (S T : Set ℕ) :
    birthLevelDomain (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) S ⊆
    birthLevelDomain (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) T ↔
      S ⊆ T :=
  birthLevelDomain_subset_iff_of_empty_requests
    (cardinalGrowth F) (cardinalGrowthBound F hMono hUnbounded)
    (singletonEmptySupportRequest_every_realStage
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton)
    S T

end BigHrushovski.CFCoherentTower
