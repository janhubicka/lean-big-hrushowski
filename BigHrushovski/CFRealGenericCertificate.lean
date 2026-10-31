import BigHrushovski.CFRealFiniteGenericity
import BigHrushovski.CFCountableDClosedChain

/-!
# The countable C_F generic: exact finite recognition data

This module collects three independently proved facts about the actual
birth-labelled graph into one interface:
* every finite subset satisfies the growth-function inequality;
* every finite subset is covered by a finite globally d-closed stage;
* every finite d-closed growth-class extension has an induced globally
  d-closed response over the literally prescribed source image.

The growth conclusion uses the *explicit* finite class-membership
and free-amalgamation assumptions of CFBatchGrowthMembership.
The response theorem uses only the real-growth assumptions.

The certificate is NOT a formal identification with the Fraisse limit.
Its remaining obligations are (1) the countable strict d-closed
back-and-forth uniqueness theorem, (2) the bridge from the published
nonnegative-domain F to the present real-domain F, and (3) stating the
class-level free-amalgamation assumption once rather than as an
assumption separately for each stage.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFGrowthNumerics

/-- Exact labelled finite extension property on the canonical real-growth
birth graph. All finite source graphs must satisfy C_F membership;
a genuinely prescribed old image, inducedness including nonedges, and
global strict d-closedness are retained. -/
def HasFiniteRealDClosedResponses
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) : Prop :=
  ∀ (V : Type) [Fintype V] [LinearOrder V],
    ∀ (H : GraphOn V) (a b : Finset V),
      H.IsGrowthSparse (cardinalGrowth F) Finset.univ →
      (hab : H.toPredimension.IsDClosed a b) →
      ∀ (e : {v : V // v ∈ a} → RealBirthVertex F hMono hUnbounded),
        Function.Injective e →
        (∀ x y : {v : V // v ∈ a},
          H.adj x.val y.val ↔
            (realCountableGraph F hMono hUnbounded).adj (e x) (e y)) →
        (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
          ((Finset.univ : Finset {v : V // v ∈ a}).image e) →
        ∃ g : {v : V // v ∈ b} → RealBirthVertex F hMono hUnbounded,
          Function.Injective g ∧
          (∀ x : {v : V // v ∈ a},
            g ⟨x.val, hab.1 x.property⟩ = e x) ∧
          (∀ x y : {v : V // v ∈ b},
            H.adj x.val y.val ↔
              (realCountableGraph F hMono hUnbounded).adj (g x) (g y)) ∧
          (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
            ((Finset.univ : Finset {v : V // v ∈ b}).image g)

/-- Fully explicit data sufficient for an abstract countable
strict d-closed genericity recognition theorem. This statement
makes no assertion about such a recognition theorem yet. -/
structure RealGrowthGenericCertificate
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) : Prop where
  growth :
    ∀ s : Finset (RealBirthVertex F hMono hUnbounded),
      cardinalGrowth F s.card ≤
        ((realCountableGraph F hMono hUnbounded).predim s : ℝ)
  closed_cover :
    ∀ s : Finset (RealBirthVertex F hMono hUnbounded),
      ∃ n : ℕ,
        s ⊆ stageImage (cardinalGrowth F)
          (cardinalGrowthBound F hMono hUnbounded) n ∧
        (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
          (stageImage (cardinalGrowth F)
            (cardinalGrowthBound F hMono hUnbounded) n)
  finite_responses : HasFiniteRealDClosedResponses F hMono hUnbounded

/-- The exact finite response half of the countable recognition
certificate. No fair schedule is required because the canonical
construction places all permitted local requests at every level. -/
theorem hasFiniteRealDClosedResponses
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) :
    HasFiniteRealDClosedResponses F hMono hUnbounded := by
  intro V _ _ H a b hGrowth hab e heInj heAdj heClosed
  exact finiteRealDClosedInterval_globalResponse
    H F hZero hMono hUnbounded hGrowth a b hab
    e heInj heAdj heClosed

/-- Assemble the existing canonical finite C_F results, without
assuming the desired countable limit identification as a premise.
The initial-stage growth and the stage-local restricted free-join
property are deliberately visible hypotheses. -/
theorem realCountableGraph_genericCertificate
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hEmpty : emptyStage.graph.IsGrowthSparse (cardinalGrowth F)
      (Finset.univ : Finset emptyStage.carrier))
    (hFree : ∀ n,
      ((stage (cardinalGrowth F)
        (cardinalGrowthBound F hMono hUnbounded) (n + 1)).graph).GrowthClosedUnderDClosedFreeJoins
          (cardinalGrowth F)) :
    RealGrowthGenericCertificate F hMono hUnbounded := by
  refine ⟨?_, ?_, ?_⟩
  · exact countableGraph_growth_of_freeJoins
      (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) hEmpty hFree
  · intro s
    obtain ⟨n, hn⟩ := finiteSet_covered
      (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) s
    exact ⟨n, hn, stageImage_global_dClosed
      (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) n⟩
  · exact hasFiniteRealDClosedResponses F hZero hMono hUnbounded


/-- The empty graph satisfies the growth inequality as soon as F(0)=0.
There are no additional initial-stage membership hypotheses. -/
theorem emptyStage_growth_of_zero
    (F : ℝ → ℝ) (hZero : F 0 = 0) :
    emptyStage.graph.IsGrowthSparse (cardinalGrowth F)
      (Finset.univ : Finset emptyStage.carrier) := by
  classical
  intro s _
  have hs : s = ∅ := by
    ext x
    exact Fin.elim0 x
  subst s
  simp [GraphOn.predim, GraphOn.edgesWithin,
    GraphOn.IsEdge, cardinalGrowth, hZero]

/-- A finite-ambient formulation of the published standing
assumption that the restricted growth class is closed under
free amalgamation over strictly d-closed substructures.
It quantifies over arbitrary finite graphs, not only the
stages already constructed. -/
def HasFiniteClassDClosedFreeJoins (F : ℕ → ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (H : GraphOn V), H.GrowthClosedUnderDClosedFreeJoins F

/-- The canonical graph satisfies all three countable genericity
criteria using one class-level free-amalgamation hypothesis, rather
than a new assumption for each finite constructed stage. -/
theorem realCountableGraph_genericCertificate_of_classFreeJoins
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : HasFiniteClassDClosedFreeJoins (cardinalGrowth F)) :
    RealGrowthGenericCertificate F hMono hUnbounded := by
  apply realCountableGraph_genericCertificate F hZero hMono hUnbounded
    (emptyStage_growth_of_zero F hZero)
  intro n
  exact hFree
    (stage (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) (n + 1)).carrier
    (stage (cardinalGrowth F)
      (cardinalGrowthBound F hMono hUnbounded) (n + 1)).graph

end CFCoherentTower
end BigHrushovski
