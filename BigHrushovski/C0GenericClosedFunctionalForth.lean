import BigHrushovski.C0FunctionalActualHomogeneity
import BigHrushovski.C0FunctionalAllClosedBaseExtension
import BigHrushovski.C0FullFunctionalClosedImages

/-!
# Track A: a general finite functional forth lemma for countable canonical C₀ models

The verified finite closed-functional forth proof for the constructed
countable limit used only three facts about its source and target:
(1) cofinal finite *literal* canonical source presentations with exact
complete unary values;
(2) cofinal finite canonical target presentations, ensuring finite
C-closed images are globally strong;
(3) the complete-functional extension property over every finite
closed base in the target.

This file states the third property explicitly and proves the same
finite forth lemma for two possibly different countable C₀ models.
No functional Fraïssé uniqueness is assumed and no chosen local
ordered representative is used.

The general theorem will support uniqueness among countable models
with precisely these canonical and extension hypotheses.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso
namespace FiniteClosedFunctionalPartialIso

/-- Exact finite functional extension over arbitrary named closed
bases in a countable graph N with complete unary operation CN.
The embeddings preserve **all** unary values and reflect adjacency;
numerical component indices of the base need not agree. -/
def HasClosedBaseFunctionalExtension
    (N : GraphOn ℕ) (CN : ℕ → Finset ℕ) : Prop :=
  ∀ (s : Finset ℕ)
    (hClosed : N.IsClosedUnderValues CN s),
    ∀ {B : Type} [Fintype B] [DecidableEq B]
      (H : GraphOn B) {m : ℕ} (κ : B → Fin m)
      (hSteps : ∀ k : ℕ, k < m →
        FiniteC0.oldStage κ k = FiniteC0.oldStage κ (k + 1) ∨
        H.toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage κ k) (FiniteC0.oldStage κ (k + 1)))
      (hSparse : H.IsTwoSparse (Finset.univ : Finset B))
      (j : {v : ℕ // v ∈ s} → B)
      (hj : Function.Injective j)
      (hAdj : ∀ a b : {v : ℕ // v ∈ s},
        N.adj a.val b.val ↔ H.adj (j a) (j b))
      (hBaseValue : ∀ a : {v : ℕ // v ∈ s},
        FiniteC0.canonicalValue H κ (j a) =
          (FiniteC0.namedClosedBaseValue CN s a).image j),
      ∃ (h : B → ℕ), Function.Injective h ∧
        (∀ a b : B, H.adj a b ↔ N.adj (h a) (h b)) ∧
        (∀ b : B,
          CN (h b) = (FiniteC0.canonicalValue H κ b).image h) ∧
        (∀ a : {v : ℕ // v ∈ s}, h (j a) = a.val)

/-- The actually constructed functional C₀ limit has this exact
property, by the previously certified arbitrary-closed-base theorem.
This is an instance, not an additional axiom or new extension proof. -/
theorem fairLimit_hasClosedBaseFunctionalExtension :
    HasClosedBaseFunctionalExtension
      FiniteFunctionalNatStage.fairGraphStages.limitGraph
      FiniteFunctionalNatStage.fairUnaryStages.limitValue := by
  intro s hClosed B _ _ H m κ hSteps hSparse j hj hAdj hValue
  exact FiniteFunctionalNatStage.fairLimit_hasFunctionalExtension_over_anyClosedBase
    s hClosed H κ hSteps hSparse j hj hAdj hValue

/-- The stage certificates themselves ensure that each literal
finite canonical stage is closed under the *ambient complete* unary
operation. No stage-monotonicity assumption is needed for this. -/
theorem canonicalStages_literalStage_closed
    (M : GraphOn ℕ) (CM : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hStages : FiniteC0.HasCanonicalFiniteStages M CM stage)
    (n : ℕ) :
    M.IsClosedUnderValues CM (stage n) := by
  classical
  obtain ⟨m, κ, _hSteps, hValues⟩ := hStages n
  let T := {v : ℕ // v ∈ stage n}
  let G : GraphOn T := M.pullback (Subtype.val : T → ℕ)
  intro x hx y hy
  let a : T := ⟨x, hx⟩
  have hyImage :
      y ∈ (FiniteC0.canonicalValue G κ a).image
        (Subtype.val : T → ℕ) := by
    rw [← hValues a]
    exact hy
  obtain ⟨b, _, hby⟩ := Finset.mem_image.mp hyImage
  exact hby ▸ b.property

/-- Any finite closed complete-functional partial isomorphism between
two (possibly different) countable canonical C₀ models extends to
cover a prescribed source vertex, provided the *target* has full
extension over arbitrary finite closed bases. The extension stays
finite, closed, globally strong, induced and complete-functional. -/
theorem canonicalFunctional_forth
    (M N : GraphOn ℕ) (CM CN : ℕ → Finset ℕ)
    (stageM stageN : ℕ → Finset ℕ)
    (hCoverM : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageM n)
    (hCoverN : ∀ s : Finset ℕ, ∃ n : ℕ, s ⊆ stageN n)
    (hStageM : FiniteC0.HasCanonicalFiniteStages M CM stageM)
    (hStageN : FiniteC0.HasCanonicalFiniteStages N CN stageN)
    (hExtN : HasClosedBaseFunctionalExtension N CN)
    (p : FiniteClosedFunctionalPartialIso M N CM CN)
    (k : ℕ) :
    ∃ q : FiniteClosedFunctionalPartialIso M N CM CN,
      Extends p q ∧ k ∈ q.graph.source := by
  classical
  obtain ⟨n, hCover⟩ := hCoverM (insert k p.graph.source)
  have hOld : p.graph.source ⊆ stageM n := by
    intro x hx
    exact hCover (Finset.mem_insert_of_mem hx)
  let T := {v : ℕ // v ∈ stageM n}
  let R := {v : ℕ // v ∈ p.graph.target}
  let G : GraphOn T :=
    M.pullback (Subtype.val : T → ℕ)
  let i : R → T := inverseStageBaseMap p (stageM n) hOld
  have hi : Function.Injective i :=
    inverseStageBaseMap_injective p (stageM n) hOld
  obtain ⟨m, κ, hSteps, hStageValues⟩ := hStageM n
  have hSparse : G.IsTwoSparse (Finset.univ : Finset T) :=
    FiniteC0.canonicalStages_literalStage_twoSparse
      M CM stageM hCoverM hStageM n
  have hAdj : ∀ a b : R,
      N.adj a.val b.val ↔ G.adj (i a) (i b) :=
    inverseStageBaseMap_induced p (stageM n) hOld
  have hBaseValue : ∀ a : R,
      FiniteC0.canonicalValue G κ (i a) =
        (FiniteC0.namedClosedBaseValue CN p.graph.target a).image i := by
    intro a
    exact inverseStageBaseMap_completeValues
      p (stageM n) hOld κ hStageValues a
  obtain ⟨h, hh, hGraph, hFull, hFix⟩ :=
    hExtN p.graph.target p.targetClosed
      G κ hSteps hSparse i hi hAdj hBaseValue
  let t : Finset ℕ := (Finset.univ : Finset T).image h
  let e : T ≃ {v : ℕ // v ∈ t} :=
    FiniteC0.imageCarrierEquiv h hh
  have hSourceClosed : M.IsClosedUnderValues CM (stageM n) :=
    canonicalStages_literalStage_closed M CM stageM hStageM n
  have hSourceStrong : M.toPredimension.IsGloballyStrong (stageM n) :=
    FiniteC0.canonicalStages_closed_globalStrong
      M CM stageM hCoverM hStageM (stageM n) hSourceClosed
  have hTargetClosed : N.IsClosedUnderValues CN t :=
    FiniteC0.fullFunctionalImage_closed
      N CN (FiniteC0.canonicalValue G κ) h hFull
  have hTargetStrong : N.toPredimension.IsGloballyStrong t :=
    FiniteC0.canonicalStages_fullFunctionalImage_globalStrong
      N CN stageN hCoverN hStageN
      (FiniteC0.canonicalValue G κ) h hFull
  let q : FiniteClosedFunctionalPartialIso M N CM CN :=
    { graph :=
        { source := stageM n
          target := t
          equiv := e
          source_global := hSourceStrong
          target_global := hTargetStrong
          induced := by
            intro a b
            exact hGraph a b }
      sourceClosed := hSourceClosed
      targetClosed := hTargetClosed
      fullValues := by
        intro a b
        have hSourceMembership :
            b.val ∈ CM a.val ↔
              b ∈ FiniteC0.canonicalValue G κ a :=
          FiniteC0.fullFunctionalImage_mem_iff
            CM (FiniteC0.canonicalValue G κ)
            (Subtype.val : T → ℕ) Subtype.val_injective
            hStageValues a b
        have hTargetMembership :
            h b ∈ CN (h a) ↔
              b ∈ FiniteC0.canonicalValue G κ a :=
          FiniteC0.fullFunctionalImage_mem_iff
            CN (FiniteC0.canonicalValue G κ)
            h hh hFull a b
        exact hSourceMembership.trans hTargetMembership.symm }
  have hTargetSub : p.graph.target ⊆ t := by
    intro x hx
    let a : R := ⟨x, hx⟩
    have hLiteral : h (i a) = x := hFix a
    exact Finset.mem_image.mpr
      ⟨i a, Finset.mem_univ _, hLiteral⟩
  refine ⟨q, ?_, hCover (Finset.mem_insert_self k p.graph.source)⟩
  refine ⟨hOld, hTargetSub, ?_⟩
  intro x
  let a : R := p.graph.equiv x
  have hPreimage : (⟨x.val, hOld x.property⟩ : T) = i a := by
    apply Subtype.ext
    change x.val = (p.graph.equiv.symm a).val
    simp [a]
  change h (⟨x.val, hOld x.property⟩ : T) = a.val
  rw [hPreimage]
  exact hFix a

end FiniteClosedFunctionalPartialIso
end FiniteStrongPartialIso
end FiniteCatalogue
end BigHrushovski
