import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness

/-!
# Finite tests recovering C_F birth-level coordinates

The original level-set topology can be recovered from the coordinate
membership tests on the actual support-saturated vertex domains.
Given finitely many levels, choose one literal empty-support birth-block
vertex at each level. Its *complete* generated b-support is precisely
that singleton level, so membership in the corresponding vertex domain
detects the requested level coordinate.

This is the inverse *finitary observation* statement complementary
to the already proved forward finite-support locality. It is not the
inverse-lifting theorem, and does not identify these support-saturated
domains with actual functional self-embedding ranges.
-/

namespace BigHrushovski.CFCoherentTower

open CFGrowthNumerics

/-- Finitely many original birth-level coordinates can be tested by
finitely many vertices of the actual countable birth carrier,
provided there is an allowed empty-support request at each level.
No singleton-*vertex* block hypothesis is made. -/
theorem birthLevelDomain_inverse_local_finset_of_empty_requests
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (t : Finset ℕ) :
    ∃ s : Finset (Vertex F K),
      ∀ (S T : Set ℕ),
        (∀ x ∈ s, (x ∈ birthLevelDomain F K S ↔
                    x ∈ birthLevelDomain F K T)) →
        ∀ n ∈ t, (n ∈ S ↔ n ∈ T) := by
  classical
  let z : ℕ → Vertex F K := fun n =>
    Classical.choose (birthLevelSupport_all_singleton_witnesses F K hReq n)
  have hz : ∀ n, birthLevelSupport F K (z n) = {n} := by
    intro n
    exact Classical.choose_spec
      (birthLevelSupport_all_singleton_witnesses F K hReq n)
  refine ⟨t.image z, ?_⟩
  intro S T hAgreement n hn
  have hzn : z n ∈ t.image z :=
    Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hTest :
      z n ∈ birthLevelDomain F K S ↔
        z n ∈ birthLevelDomain F K T :=
    hAgreement (z n) hzn
  have hMembership (A : Set ℕ) :
      z n ∈ birthLevelDomain F K A ↔ n ∈ A := by
    change (∀ q ∈ birthLevelSupport F K (z n), q ∈ A) ↔ n ∈ A
    rw [hz n]
    simp
  exact (hMembership S).symm.trans
    (hTest.trans (hMembership T))

/-- The same finite inverse-coordinate statement in the paper's
real-growth class, with the exact empty-base and singleton
hypotheses that produce actual empty-support stage requests. -/
theorem realBirthLevelDomain_inverse_local_finset
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2)
    (t : Finset ℕ) :
    ∃ s : Finset (Vertex (cardinalGrowth F)
        (cardinalGrowthBound F hMono hUnbounded)),
      ∀ (S T : Set ℕ),
        (∀ x ∈ s,
          (x ∈ birthLevelDomain (cardinalGrowth F)
              (cardinalGrowthBound F hMono hUnbounded) S ↔
           x ∈ birthLevelDomain (cardinalGrowth F)
              (cardinalGrowthBound F hMono hUnbounded) T)) →
        ∀ n ∈ t, (n ∈ S ↔ n ∈ T) :=
  birthLevelDomain_inverse_local_finset_of_empty_requests
    (cardinalGrowth F) (cardinalGrowthBound F hMono hUnbounded)
    (singletonEmptySupportRequest_every_realStage
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton) t

end BigHrushovski.CFCoherentTower
