import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness
import RamseySpace.Examples.SupportedEllentuck

/-!
# The concrete C_F supported-domain Ramsey space

We now import the already formalized classical Ellentuck space
transport instead of duplicating its A.1--A.4 or Tychonoff
closedness arguments. The concrete instance uses the exact
finite support obtained from the whole generated b-closure
of every vertex in the actual C_F birth presentation.

Empty-support requests supply a vertex whose full birth-level
support is precisely {n} at every n. This suffices to identify
the synthetic family of complete-support domains with
increasing level enumerations, and to transport the published
Ramsey-space axioms, Tychonoff closedness of approximation
codes, and the Ellentuck theorem.

These are assertions for the *synthetic supported-domain*
point type. Identifying that point type with the ranges of
all genuine ordered partial R/H self-embeddings is a separate
concrete theorem in the current Track E integration stack.
-/

namespace BigHrushovski.CFCoherentTower

open CFGrowthNumerics CFStageCatalogue

/-- Choose a genuine birth vertex on each level with precisely
singleton complete birth-level support. The witnesses are
derived from actual empty-support requests of the C_F tower. -/
noncomputable def supportedSingletonWitness
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) (n : ℕ) : Vertex F K :=
  Classical.choose
    (birthLevelSupport_all_singleton_witnesses F K hReq n)

theorem supportedSingletonWitness_spec
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) (n : ℕ) :
    birthLevelSupport F K
      (supportedSingletonWitness F K hReq n) = {n} :=
  Classical.choose_spec
    (birthLevelSupport_all_singleton_witnesses F K hReq n)

/-- The existing supported-Ellentuck approximation system
instantiated with the genuine full generated birth-level
supports of the countable C_F construction. -/
noncomputable def actualSupportedApproximationSystem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) : RamseySpace.ApproximationSystem :=
  RamseySpace.Examples.SupportedEllentuck.approximationSystem
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq)

/-- The supported-domain representation is literal equality
with U[range(X)] on the original C_F vertex carrier. -/
theorem actualSupportedDomain_ofPoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (X : RamseySpace.Examples.Ellentuck.Point) :
    (RamseySpace.Examples.SupportedEllentuck.ofPoint
      (birthLevelSupport F K) X).val =
      birthLevelDomain F K (Set.range X) := rfl

/-- The transported quasi-order really is inclusion of the
actual complete-support vertex subsets, not an invented
order on finite code records. -/
theorem actualSupported_le_iff_domain_subset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (D E : RamseySpace.Examples.SupportedEllentuck.Copy
      (birthLevelSupport F K)) :
    (actualSupportedApproximationSystem F K hReq).le D E ↔
      D.1 ⊆ E.1 :=
  RamseySpace.Examples.SupportedEllentuck.le_iff_domain_subset
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq) D E

/-- The finite approximation of U[range(X)] is precisely
the ordinary first-n image-level approximation of X. -/
theorem actualSupported_approx_ofPoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (X : RamseySpace.Examples.Ellentuck.Point) (n : ℕ) :
    (actualSupportedApproximationSystem F K hReq).approx n
      (RamseySpace.Examples.SupportedEllentuck.ofPoint
        (birthLevelSupport F K) X) =
      RamseySpace.Examples.Ellentuck.approx n X :=
  RamseySpace.Examples.SupportedEllentuck.approx_ofPoint
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq) X n

/-- Published A.1--A.4 for the actual finite-support presentation
of the synthetic C_F domain space, transported from classical
Ellentuck rather than reconstructed by another fusion argument. -/
noncomputable def actualSupported_ramseySpace
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    RamseySpace.AbstractRamseySpace
      (actualSupportedApproximationSystem F K hReq) :=
  RamseySpace.Examples.SupportedEllentuck.ramseySpace
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq)

/-- Tychonoff closedness of the approximation-*code image*.
This is stronger and different from the already certified
closedness of all support-saturated vertex domains in 2^V. -/
theorem actualSupported_isTychonoffClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    (actualSupportedApproximationSystem F K hReq).IsTychonoffClosed :=
  RamseySpace.Examples.SupportedEllentuck.isTychonoffClosed
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq)

/-- Ellentuck's theorem for the supported-domain space over
the actual C_F finite generated supports and increasing levels.
This does not yet claim a theorem about arbitrary R/H copy
domains without the concrete point-equivalence bridge. -/
theorem actualSupported_Ellentuck
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := actualSupportedApproximationSystem F K hReq) :=
  RamseySpace.Examples.SupportedEllentuck.supportedEllentuck
    (birthLevelSupport F K)
    (supportedSingletonWitness F K hReq)
    (supportedSingletonWitness_spec F K hReq)

/-- The real-growth C_F assumptions of the manuscript supply
all required singleton-level support witnesses. The synthetic
omega-level supported-domain space therefore satisfies
the full classical Ellentuck conclusion unconditionally
under these explicitly stated numeric/class hypotheses. -/
theorem realSupported_Ellentuck
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (cardinalGrowth F))
    (hSingleton : F 1 ≤ 2) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := actualSupportedApproximationSystem
        (cardinalGrowth F)
        (cardinalGrowthBound F hMono hUnbounded)
        (singletonEmptySupportRequest_every_realStage
          F hZero hMono hUnbounded hFree hEmptyClass hSingleton)) :=
  actualSupported_Ellentuck
    (cardinalGrowth F)
    (cardinalGrowthBound F hMono hUnbounded)
    (singletonEmptySupportRequest_every_realStage
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton)

end BigHrushovski.CFCoherentTower
