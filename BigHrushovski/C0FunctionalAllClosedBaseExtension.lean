import BigHrushovski.C0TwoSidedEmbeddedAmalgam
import BigHrushovski.C0FunctionalNamedBaseResponse
import BigHrushovski.C0NamedClosedBaseValues

/-!
# Track A: the actual C₀ functional limit has extension over every finite closed base

The constructed countable functional C₀ limit already realizes every
finite canonical extension over its literal finite canonical stages.
A finite unary-closed base A need not be a stage, but it lies in one.

Given a finite canonical functional extension B of A, normalize the
two arbitrary embeddings A → S and A → B, where S is a chosen enclosing
stage. The certified two-sided free amalgam produces one finite
canonical structure K into which both embed with their complete unary
functions unchanged. Realizing K over the whole stage S and restricting
to B gives a full induced functional embedding B into the countable
limit fixing A pointwise.

No arbitrary component-index agreement over A is needed. The named
base function is its actual *entire* unary value, and exact equality
of these values is the only functional compatibility assumption.

This theorem is about the unordered finite functional age. Strong
homogeneity, uniqueness and the uniform local ordered expansion are
separate conclusions, not asserted here.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- The actual fair C₀ limit answers finite canonical functional
extensions over **every** finite closed subset of its vertex carrier,
not only its originally constructed canonical stages.

The finite requested structure B has its own canonical index κB
with empty or minimal strong steps and is 2-sparse. The original base
is the literal subtype of a finite set s closed under the whole
countable unary operation. Its embedding into B preserves and
reflects the graph and transports the entire named complete value.

The resulting map B → ℕ simultaneously preserves and reflects edges,
preserves the complete finite-valued unary function, and fixes the
original finite base pointwise. -/
theorem fairLimit_hasFunctionalExtension_over_anyClosedBase
    (s : Finset ℕ)
    (hClosed :
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue s)
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    {m : ℕ} (κB : B → Fin m)
    (hStepsB : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κB k =
        FiniteC0.oldStage κB (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κB k)
        (FiniteC0.oldStage κB (k + 1)))
    (hSparseB : H.IsTwoSparse (Finset.univ : Finset B))
    (j : {v : ℕ // v ∈ s} → B)
    (hj : Function.Injective j)
    (hAdj : ∀ a b : {v : ℕ // v ∈ s},
      fairGraphStages.limitGraph.adj a.val b.val ↔
        H.adj (j a) (j b))
    (hValueB : ∀ a : {v : ℕ // v ∈ s},
      FiniteC0.canonicalValue H κB (j a) =
        (FiniteC0.namedClosedBaseValue
          fairUnaryStages.limitValue s a).image j) :
    ∃ h : B → ℕ,
      Function.Injective h ∧
      (∀ a b : B,
        H.adj a b ↔ fairGraphStages.limitGraph.adj (h a) (h b)) ∧
      (∀ b : B,
        fairUnaryStages.limitValue (h b) =
          (FiniteC0.canonicalValue H κB b).image h) ∧
      (∀ a : {v : ℕ // v ∈ s}, h (j a) = a.val) := by
  classical
  let N : GraphOn ℕ := fairGraphStages.limitGraph
  let C : ℕ → Finset ℕ := fairUnaryStages.limitValue
  obtain ⟨n, hSn⟩ := fairCoherentC0Stages.finite_stage_cover s
  let T := {v : ℕ // v ∈ fairGraphStages.stage n}
  let A := {v : ℕ // v ∈ s}
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  let i : A → T :=
    FiniteC0.closedBaseStageInclusion s (fairGraphStages.stage n) hSn
  have hi : Function.Injective i :=
    FiniteC0.closedBaseStageInclusion_injective
      s (fairGraphStages.stage n) hSn
  obtain ⟨p, κOld, hStepsOld, hOldValues⟩ :=
    fairLimitCanonicalStages n
  have hStageSparse : G.IsTwoSparse (Finset.univ : Finset T) :=
    FiniteC0.canonicalStages_literalStage_twoSparse
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages n
  let F : A → Finset A :=
    FiniteC0.namedClosedBaseValue C s
  have hValueOld : ∀ a : A,
      FiniteC0.canonicalValue G κOld (i a) =
        (F a).image i := by
    intro a
    exact FiniteC0.canonicalStage_complete_namedBase_values
      N C (fairGraphStages.stage n) s hSn hClosed
      κOld hOldValues a
  have hAdjBase : ∀ a b : A,
      G.adj (i a) (i b) ↔ H.adj (j a) (j b) := by
    intro a b
    exact hAdj a b
  let K : GraphOn
      (TaggedAmalgam.Carrier A
        (FiniteSpan.Tail i) (FiniteSpan.Tail j)) :=
    TaggedAmalgam.freeGraph
      (FiniteSpan.normalGraph G i hi)
      (FiniteSpan.normalGraph H j hj)
  let f : T → TaggedAmalgam.Carrier A
        (FiniteSpan.Tail i) (FiniteSpan.Tail j) :=
    FiniteSpan.leftAmalgamEmbedding i hi j
  let g : B → TaggedAmalgam.Carrier A
        (FiniteSpan.Tail i) (FiniteSpan.Tail j) :=
    FiniteSpan.rightAmalgamEmbedding i j hj
  obtain ⟨q, θ, hSparseK, hStrongL, hStrongR,
      hStepsK, hGraphL, hGraphR, hBase, hOnly,
      hCompleteL, hCompleteR⟩ :=
    FiniteSpan.exists_twoSidedCanonicalFunctionalAmalgam
      G H i j hi hj hAdjBase
      hStageSparse hSparseB
      κOld κB hStepsOld hStepsB F
      hValueOld hValueB
  have hf : Function.Injective f :=
    FiniteSpan.leftAmalgamEmbedding_injective i hi j
  have hg : Function.Injective g :=
    FiniteSpan.rightAmalgamEmbedding_injective i j hj
  have hAdjStage : ∀ a b : T,
      N.adj a.val b.val ↔ K.adj (f a) (f b) := by
    intro a b
    exact (hGraphL a b).symm
  have hAdjRight : ∀ a b : B,
      H.adj a b ↔ K.adj (g a) (g b) := by
    intro a b
    exact (hGraphR a b).symm
  exact exists_functionalExtension_over_named_closedBase_of_stageAmalgam
    n p κOld hOldValues
    K θ hStepsK f hf hAdjStage hCompleteL
    H κB g hg hAdjRight hCompleteR i j hBase

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
