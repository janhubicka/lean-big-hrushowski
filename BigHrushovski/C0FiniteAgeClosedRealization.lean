import BigHrushovski.C0FunctionalAgeUniversality
import BigHrushovski.C0FullFunctionalClosedImages

/-!
# Track A: realizing the exact finite functional C₀ age as closed substructures

The actual countable functional C₀ limit is universal for finite
canonical C₀ presentations. The universal embedding is a complete-
functional embedding, so its finite image is automatically closed
under the complete one-generated unary operation and globally strong.

Moreover, the original finite canonical index transports to the
*literal induced graph on that image*, preserving both all empty-or-
minimal strong component steps and every complete canonical value.
There is no need to choose a new component enumeration.

Together with the separate finite-closed hereditary theorem this
provides the two directions of the finite functional age description.
Neither assertion selects the uniform local orders required by the
Ramsey expansion.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Every finite canonical functional C₀ structure occurs in the
actual limit as a **closed and globally strong** finite induced
substructure. Both induced adjacency and complete unary values are
preserved by one injective map; this is stronger than graph-only age
universality. -/
theorem fairLimit_realizesFiniteCanonicalAsClosedStrong
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    {m : ℕ} (κ : B → Fin m)
    (hSteps : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κ k =
        FiniteC0.oldStage κ (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k)
        (FiniteC0.oldStage κ (k + 1)))
    (hSparse : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ (f : B → ℕ),
      Function.Injective f ∧
      (∀ u v : B,
        H.adj u v ↔ fairGraphStages.limitGraph.adj (f u) (f v)) ∧
      (∀ u : B,
        fairUnaryStages.limitValue (f u) =
          (FiniteC0.canonicalValue H κ u).image f) ∧
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue ((Finset.univ : Finset B).image f) ∧
      fairGraphStages.limitGraph.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset B).image f) := by
  classical
  obtain ⟨f, hf, hAdj, hFull⟩ :=
    fairLimit_universalForFiniteFunctionalC0 H κ hSteps hSparse
  refine ⟨f, hf, hAdj, hFull, ?_, ?_⟩
  · exact FiniteC0.fullFunctionalImage_closed
      fairGraphStages.limitGraph fairUnaryStages.limitValue
      (FiniteC0.canonicalValue H κ) f hFull
  · exact FiniteC0.canonicalStages_fullFunctionalImage_globalStrong
      fairGraphStages.limitGraph fairUnaryStages.limitValue
      fairGraphStages.stage fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages
      (FiniteC0.canonicalValue H κ) f hFull

/-- The *same* universal embedding transports the finite canonical
component index to the literal induced finite image, preserving
every empty-or-minimal strong stage and the entire canonical unary
operation. No finite component-compression or new order choice occurs. -/
theorem fairLimit_realizesFiniteCanonicalImagePresentation
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    {m : ℕ} (κ : B → Fin m)
    (hSteps : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κ k =
        FiniteC0.oldStage κ (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k)
        (FiniteC0.oldStage κ (k + 1)))
    (hSparse : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ (f : B → ℕ) (hf : Function.Injective f),
      (∀ u v : B,
        H.adj u v ↔ fairGraphStages.limitGraph.adj (f u) (f v)) ∧
      (∀ u : B,
        fairUnaryStages.limitValue (f u) =
          (FiniteC0.canonicalValue H κ u).image f) ∧
      (let a : Finset ℕ := (Finset.univ : Finset B).image f
       let K : GraphOn {w : ℕ // w ∈ a} :=
         fairGraphStages.limitGraph.pullback
           (Subtype.val : {w : ℕ // w ∈ a} → ℕ)
       let e : B ≃ {w : ℕ // w ∈ a} :=
         FiniteC0.imageCarrierEquiv f hf
       let κa : {w : ℕ // w ∈ a} → Fin m :=
         FiniteC0.relabelIndex κ e
       (∀ k : ℕ, k < m →
         FiniteC0.oldStage κa k = FiniteC0.oldStage κa (k + 1) ∨
         K.toPredimension.IsMinimalStrongStep
           (FiniteC0.oldStage κa k) (FiniteC0.oldStage κa (k + 1))) ∧
       (∀ u : B,
         (FiniteC0.canonicalValue K κa (e u)).image
           (Subtype.val : {w : ℕ // w ∈ a} → ℕ) =
         (FiniteC0.canonicalValue H κ u).image f)) := by
  classical
  obtain ⟨f, hf, hAdj, hFull⟩ :=
    fairLimit_universalForFiniteFunctionalC0 H κ hSteps hSparse
  refine ⟨f, hf, hAdj, hFull, ?_⟩
  exact FiniteC0.canonicalPresentation_on_image
    H fairGraphStages.limitGraph f hf hAdj κ hSteps

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
