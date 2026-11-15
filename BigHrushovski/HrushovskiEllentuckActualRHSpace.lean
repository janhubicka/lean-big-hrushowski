import BigHrushovski.HrushovskiEllentuckActualLevelAction
import BigHrushovski.HrushovskiEllentuckActualSupportedSpace

/-!
# The omega-level Ellentuck space of actual ordered C_F functional copies

The preceding verified finite uniqueness/limit-lifting theorem
identifies actual ordered partial R/H self-embedding ranges with
complete-support domains over increasing image-level sets,
provided every birth level is represented. The separate library
instance identifies precisely those domains with classical
Ellentuck points, preserving their first-n level approximations.

We now make this a literal equivalence of point types and
transport the complete approximation system, including its order,
published A.1--A.4, Tychonoff closedness and the textbook
Ellentuck theorem.

The actual R/H embedding predicate includes the named
birth-level preorder and the canonical order. The theorem does
not classify embeddings of an unnamed reduct. It also does
not independently show that the product topology on all
characteristic functions of vertex domains agrees with the
metric topology of the approximation system; that is a
separate topological comparison in the manuscript.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue CFGrowthNumerics

/-- The genuine ordered partial R/H copies, as literal subsets
of the *original* countable birth vertex carrier. -/
def ActualOrderedRHCopy
    (F : ℕ → ℝ) (K : ℕ → ℕ) :=
  {D : Set (Vertex F K) // D ∈ AllOrderedRHCopyDomains F K}

/-- An actual ordered R/H copy domain is precisely one of the
synthetic supported Ellentuck domains, and conversely. This
is a theorem about *all* ordered functional copy ranges,
not merely a selected canonical lift. -/
theorem actualRHCopy_mem_iff_supportedPoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (D : Set (Vertex F K)) :
    D ∈ AllOrderedRHCopyDomains F K ↔
      ∃ X : RamseySpace.Examples.Ellentuck.Point,
        RamseySpace.Examples.SupportedEllentuck.domain
          (birthLevelSupport F K) X = D := by
  rw [allOrderedRHCopyDomains_eq_supported F K hReq]
  constructor
  · rintro ⟨h, hh, hD⟩
    refine ⟨OrderEmbedding.ofStrictMono h hh, ?_⟩
    change birthLevelDomain F K (Set.range h) = D
    exact hD
  · rintro ⟨X, hD⟩
    refine ⟨fun n => X n, X.strictMono, ?_⟩
    change birthLevelDomain F K (Set.range X) = D
    exact hD

/-- The literal copy-domain identification, as an equivalence
preserving the underlying vertex subset pointwise. -/
noncomputable def actualRHCopy_equiv_supported
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    ActualOrderedRHCopy F K ≃
      RamseySpace.Examples.SupportedEllentuck.Copy
        (birthLevelSupport F K) where
  toFun := fun D =>
    ⟨D.1, (actualRHCopy_mem_iff_supportedPoint F K hReq D.1).mp D.2⟩
  invFun := fun D =>
    ⟨D.1, (actualRHCopy_mem_iff_supportedPoint F K hReq D.1).mpr D.2⟩
  left_inv := by intro D; exact Subtype.ext rfl
  right_inv := by intro D; exact Subtype.ext rfl

/-- The finite approximation system of genuine ordered R/H
copy domains. By definition this is the *exact pointwise*
transport of the existing synthetic supported-domain system,
so the first-n approximations are preserved literally. -/
noncomputable def actualRHCopyApproximationSystem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    RamseySpace.ApproximationSystem :=
  (actualSupportedApproximationSystem F K hReq).reindex
    (actualRHCopy_equiv_supported F K hReq)

/-- The refinement relation on genuine ordered R/H copies
is exactly inclusion of their literal vertex domains. -/
theorem actualRHCopy_le_iff_subset
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (D E : ActualOrderedRHCopy F K) :
    (actualRHCopyApproximationSystem F K hReq).le D E ↔
      D.1 ⊆ E.1 := by
  change
    (actualSupportedApproximationSystem F K hReq).le
      (actualRHCopy_equiv_supported F K hReq D)
      (actualRHCopy_equiv_supported F K hReq E) ↔
      D.1 ⊆ E.1
  exact actualSupported_le_iff_domain_subset F K hReq _ _

/-- A basic Ellentuck neighborhood in the *actual* ordered R/H
copy-domain space has exactly the manuscript's two conditions:
the literal vertex domain refines the reference copy by inclusion,
and its first-n level approximation equals the prescribed prefix.
The second condition is not to be confused with equality of
all vertex characteristic functions through a fixed stage. -/
theorem actualRHCopy_mem_basicNeighborhood_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (n : ℕ) (a : RamseySpace.Examples.Ellentuck.Approx n)
    (D B : ActualOrderedRHCopy F K) :
    D ∈ (actualRHCopyApproximationSystem F K hReq).neighborhood a B ↔
      D.1 ⊆ B.1 ∧
        (actualRHCopyApproximationSystem F K hReq).approx n D = a := by
  rw [RamseySpace.ApproximationSystem.mem_neighborhood,
    actualRHCopy_le_iff_subset F K hReq D B]

/-- Finite approximations of a genuine copy whose level
enumeration is X are literally the first n levels of X,
not an isomorphic replacement finite diagram. -/
theorem actualRHCopy_approx_ofPoint
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (X : RamseySpace.Examples.Ellentuck.Point) (n : ℕ) :
    (actualRHCopyApproximationSystem F K hReq).approx n
      ((actualRHCopy_equiv_supported F K hReq).symm
        (RamseySpace.Examples.SupportedEllentuck.ofPoint
          (birthLevelSupport F K) X)) =
        RamseySpace.Examples.Ellentuck.approx n X := by
  change
    (actualSupportedApproximationSystem F K hReq).approx n
      ((actualRHCopy_equiv_supported F K hReq)
        ((actualRHCopy_equiv_supported F K hReq).symm
          (RamseySpace.Examples.SupportedEllentuck.ofPoint
            (birthLevelSupport F K) X))) =
      RamseySpace.Examples.Ellentuck.approx n X
  simpa using actualSupported_approx_ofPoint F K hReq X n

/-- The named ordered R/H copy-domain space satisfies the
published A.1--A.4 axioms with its literal first-n level
approximations. This is transport by the concrete copy
equivalence, not an unverified new fusion construction. -/
noncomputable def actualRHCopy_ramseySpace
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    RamseySpace.AbstractRamseySpace
      (actualRHCopyApproximationSystem F K hReq) :=
  (actualSupported_ramseySpace F K hReq).reindex
    (actualRHCopy_equiv_supported F K hReq)

/-- Tychonoff closedness of the actual R/H copy
approximation-code image (NOT the Cantor cube of all
complete-support vertex domains). -/
theorem actualRHCopy_isTychonoffClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    (actualRHCopyApproximationSystem F K hReq).IsTychonoffClosed :=
  (actualSupportedApproximationSystem F K hReq).reindex_isTychonoffClosed
    (actualRHCopy_equiv_supported F K hReq)
    (actualSupported_isTychonoffClosed F K hReq)

/-- The textbook Ellentuck theorem for the spaces of actual
ordered partial R/H self-embedding ranges of the countable C_F
birth presentation, with the concrete first-n image-level
approximation system. -/
theorem actualRHCopy_Ellentuck
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := actualRHCopyApproximationSystem F K hReq) :=
  RamseySpace.abstractEllentuck_reindex
    (actualSupported_ramseySpace F K hReq)
    (actualSupported_isTychonoffClosed F K hReq)
    (actualRHCopy_equiv_supported F K hReq)

/-- Under the real-growth, free-join, empty-base and singleton
admissibility hypotheses of the C_F manuscript, the actual ordered
partial R/H functional copy-domain space satisfies the textbook
Ellentuck theorem. Every level is genuinely represented by an
empty-support request; no witness axiom is left in the statement. -/
theorem realActualRHCopy_Ellentuck
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (CFGrowthNumerics.cardinalGrowth F))
    (hEmptyClass : EmptyDClosedInGrowthClass (CFGrowthNumerics.cardinalGrowth F))
    (hSingleton : F 1 ≤ 2) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := actualRHCopyApproximationSystem
        (CFGrowthNumerics.cardinalGrowth F)
        (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
        (singletonEmptySupportRequest_every_realStage
          F hZero hMono hUnbounded hFree hEmptyClass hSingleton)) :=
  actualRHCopy_Ellentuck
    (CFGrowthNumerics.cardinalGrowth F)
    (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
    (singletonEmptySupportRequest_every_realStage
      F hZero hMono hUnbounded hFree hEmptyClass hSingleton)

end BigHrushovski.CFCoherentTower
