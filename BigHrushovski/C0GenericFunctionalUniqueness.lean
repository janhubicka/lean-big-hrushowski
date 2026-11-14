import BigHrushovski.C0GenericClosedFunctionalForth

/-!
# Track A: uniqueness of the countable canonical functional C₀ limit

Let (M,CM) and (N,CN) be countable functional C₀ structures with
cofinal literal finite canonical presentations carrying exactly their
complete one-generated unary values. Suppose *both* have the full
functional extension property over arbitrary finite closed bases.

The verified parameterized finite forth lemma extends any finite
closed functional partial isomorphism to include a prescribed
source vertex. Applying it to the inverse gives a back step.
Composing the two yields the genuine finite joint extension
property; the existing certified functional back-and-forth theorem
then produces an isomorphism of the complete functional structures
extending any initial finite closed functional partial isomorphism.

The empty finite partial isomorphism exists because the finite
canonical stages imply 2-sparsity. Hence these hypotheses determine
a unique countable functional model up to isomorphism. No graph-
reduct-only uniqueness result or chosen local component order is
substituted for the full functional conclusion.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso
namespace FiniteClosedFunctionalPartialIso

/-- Two countable canonical C₀ models with the full finite
closed-functional extension property satisfy a **joint** finite
closed-functional back-and-forth step. The components and values
of the models may have different original numerical labels. -/
theorem canonicalFunctional_hasJointSteps
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ)
    (stageM stageN : ℕ → Finset ℕ)
    (hCoverM : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageM n)
    (hCoverN : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageN n)
    (hStageM : FiniteC0.HasCanonicalFiniteStages M CM stageM)
    (hStageN : FiniteC0.HasCanonicalFiniteStages N CN stageN)
    (hExtM : HasClosedBaseFunctionalExtension M CM)
    (hExtN : HasClosedBaseFunctionalExtension N CN) :
    HasJointSteps M N CM CN := by
  intro k p
  obtain ⟨q, hpq, hkSource⟩ :=
    canonicalFunctional_forth
      M N CM CN stageM stageN
      hCoverM hCoverN hStageM hStageN hExtN p k
  obtain ⟨r, hqr, hkBackSource⟩ :=
    canonicalFunctional_forth
      N M CN CM stageN stageM
      hCoverN hCoverM hStageN hStageM hExtM q.symm k
  have hBack : Extends q r.symm := by
    have h := Extends_symm hqr
    simpa [Extends, symm, FiniteStrongPartialIso.symm] using h
  refine ⟨r.symm, ?_, ?_, ?_⟩
  · exact FiniteStrongPartialIso.Extends.trans hpq hBack
  · exact hBack.1 hkSource
  · change k ∈ r.graph.source
    exact hkBackSource

/-- Every finite closed complete-functional partial isomorphism
between the two models extends to a single **full functional**
isomorphism of their countable carriers, preserving and reflecting
the whole graph and transporting all complete unary values. -/
theorem canonicalFunctional_equiv_extending
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ)
    (stageM stageN : ℕ → Finset ℕ)
    (hCoverM : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageM n)
    (hCoverN : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageN n)
    (hStageM : FiniteC0.HasCanonicalFiniteStages M CM stageM)
    (hStageN : FiniteC0.HasCanonicalFiniteStages N CN stageN)
    (hExtM : HasClosedBaseFunctionalExtension M CM)
    (hExtN : HasClosedBaseFunctionalExtension N CN)
    (p : FiniteClosedFunctionalPartialIso M N CM CN) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ, M.adj x y ↔ N.adj (e x) (e y)) ∧
      (∀ x : ℕ, CN (e x) = (CM x).image e) ∧
      (∀ x : ℕ, ∀ hx : x ∈ p.graph.source,
        e x = (p.graph.equiv ⟨x, hx⟩).val) := by
  exact exists_functional_equiv_extending p
    (canonicalFunctional_hasJointSteps
      M N CM CN stageM stageN
      hCoverM hCoverN hStageM hStageN hExtM hExtN)

/-- Every two countable canonical functional C₀ models satisfying
the same full finite closed-base extension property are isomorphic
as **complete functional** structures.

No assumption that the two graph reducts have been identified with
a separate generic graph is required. 2-sparsity and the empty
globally strong base follow from the exact canonical-stage
certificates. -/
theorem canonicalFunctional_unique
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ)
    (stageM stageN : ℕ → Finset ℕ)
    (hCoverM : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageM n)
    (hCoverN : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageN n)
    (hStageM : FiniteC0.HasCanonicalFiniteStages M CM stageM)
    (hStageN : FiniteC0.HasCanonicalFiniteStages N CN stageN)
    (hExtM : HasClosedBaseFunctionalExtension M CM)
    (hExtN : HasClosedBaseFunctionalExtension N CN) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ, M.adj x y ↔ N.adj (e x) (e y)) ∧
      (∀ x : ℕ, CN (e x) = (CM x).image e) := by
  classical
  have hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s :=
    FiniteC0.sparse_of_canonicalFiniteStages
      M CM stageM hCoverM hStageM
  have hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s :=
    FiniteC0.sparse_of_canonicalFiniteStages
      N CN stageN hCoverN hStageN
  let g0 : FiniteStrongPartialIso M N :=
    FiniteStrongPartialIso.empty M N hSparseM hSparseN
  let p0 : FiniteClosedFunctionalPartialIso M N CM CN :=
    { graph := g0
      sourceClosed := by
        change M.IsClosedUnderValues CM (∅ : Finset ℕ)
        intro x hx
        simp at hx
      targetClosed := by
        change N.IsClosedUnderValues CN (∅ : Finset ℕ)
        intro x hx
        simp at hx
      fullValues := by
        intro x y
        have hx : x.val ∈ (∅ : Finset ℕ) := x.property
        simp at hx }
  obtain ⟨e, hAdj, hValue, _⟩ :=
    canonicalFunctional_equiv_extending
      M N CM CN stageM stageN
      hCoverM hCoverN hStageM hStageN hExtM hExtN p0
  exact ⟨e, hAdj, hValue⟩

/-- The *constructed* countable functional C₀ model is uniquely
determined, among countable models admitting cofinal canonical
stages and the exact finite closed-functional extension property,
by those two conditions. The isomorphism preserves complete unary
values, not merely its graph reduct. -/
theorem canonicalFunctional_isomorphic_to_fairLimit
    (M : GraphOn ℕ) (CM : ℕ → Finset ℕ)
    (stageM : ℕ → Finset ℕ)
    (hCoverM : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageM n)
    (hStageM : FiniteC0.HasCanonicalFiniteStages M CM stageM)
    (hExtM : HasClosedBaseFunctionalExtension M CM) :
    ∃ e : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        M.adj x y ↔
          FiniteFunctionalNatStage.fairGraphStages.limitGraph.adj
            (e x) (e y)) ∧
      (∀ x : ℕ,
        FiniteFunctionalNatStage.fairUnaryStages.limitValue (e x) =
          (CM x).image e) := by
  exact canonicalFunctional_unique
    M FiniteFunctionalNatStage.fairGraphStages.limitGraph
    CM FiniteFunctionalNatStage.fairUnaryStages.limitValue
    stageM FiniteFunctionalNatStage.fairGraphStages.stage
    hCoverM FiniteFunctionalNatStage.fairCoherentC0Stages.finite_stage_cover
    hStageM FiniteFunctionalNatStage.fairLimitCanonicalStages
    hExtM fairLimit_hasClosedBaseFunctionalExtension

end FiniteClosedFunctionalPartialIso
end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
