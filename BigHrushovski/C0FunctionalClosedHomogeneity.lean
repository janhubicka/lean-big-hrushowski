import BigHrushovski.C0FunctionalActualHomogeneity

/-!
# Track A: homogeneity of the actual C₀ functional limit over closed sets

The preceding theorem extends every finite closed functional partial
isomorphism which also carries explicit global-strongness certificates.
In the actual countable C₀ limit, however, every finite substructure
closed under the *entire* unary operation is automatically globally
strong, by the certified canonical-stage theorem.

We therefore obtain the usual homogeneity assertion in the finite
closed-substructure language: every isomorphism between two finite
C-closed substructures extends to an automorphism of the countable
graph together with its complete set-valued unary operation. The
source and target need not be canonical stages or initial segments.

This theorem concerns the unordered functional structure. Selecting
the uniform local orders of the paper's Ramsey expansion is a
separate issue.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Any finite closed *functional* isomorphism of the actual countable
C₀ limit extends to an automorphism preserving and reflecting the
graph and transporting the entire complete unary value of every
vertex. No explicit strongness assumption on the finite domains
is needed: closedness supplies it via canonical finite stages. -/
theorem fairLimit_functionalHomogeneity_closedSubstructures
    (s t : Finset ℕ)
    (hClosedS :
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue s)
    (hClosedT :
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue t)
    (e : {x : ℕ // x ∈ s} ≃ {x : ℕ // x ∈ t})
    (hAdj : ∀ u v : {x : ℕ // x ∈ s},
      fairGraphStages.limitGraph.adj u.val v.val ↔
        fairGraphStages.limitGraph.adj (e u).val (e v).val)
    (hUnary : ∀ u v : {x : ℕ // x ∈ s},
      v.val ∈ fairUnaryStages.limitValue u.val ↔
        (e v).val ∈ fairUnaryStages.limitValue (e u).val) :
    ∃ h : ℕ ≃ ℕ,
      (∀ x y : ℕ,
        fairGraphStages.limitGraph.adj x y ↔
          fairGraphStages.limitGraph.adj (h x) (h y)) ∧
      (∀ x : ℕ,
        fairUnaryStages.limitValue (h x) =
          (fairUnaryStages.limitValue x).image h) ∧
      (∀ u : {x : ℕ // x ∈ s}, h u.val = (e u).val) := by
  let N : GraphOn ℕ := fairGraphStages.limitGraph
  let C : ℕ → Finset ℕ := fairUnaryStages.limitValue
  have hStrongS : N.toPredimension.IsGloballyStrong s :=
    FiniteC0.canonicalStages_closed_globalStrong
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages s hClosedS
  have hStrongT : N.toPredimension.IsGloballyStrong t :=
    FiniteC0.canonicalStages_closed_globalStrong
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages t hClosedT
  let p : FiniteStrongPartialIso.FiniteClosedFunctionalPartialIso
      N N C C :=
    { graph :=
        { source := s
          target := t
          equiv := e
          source_global := hStrongS
          target_global := hStrongT
          induced := hAdj }
      sourceClosed := hClosedS
      targetClosed := hClosedT
      fullValues := hUnary }
  obtain ⟨h, hGraph, hValues, hOld⟩ :=
    FiniteStrongPartialIso.FiniteClosedFunctionalPartialIso.fairLimit_functionalHomogeneous p
  refine ⟨h, hGraph, hValues, ?_⟩
  intro u
  exact hOld u.val u.property

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
