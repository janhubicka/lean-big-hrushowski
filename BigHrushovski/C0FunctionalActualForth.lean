import BigHrushovski.C0FunctionalPartialBaseTransport
import BigHrushovski.C0FunctionalAllClosedBaseExtension
import BigHrushovski.C0FullFunctionalClosedImages

/-!
# Track A: an actual closed functional forth step in the countable C₀ limit

Given a finite closed complete-functional partial isomorphism p of the
constructed countable C₀ limit, and a prescribed next source vertex k,
choose a finite canonical stage T containing both k and the old source.
The inverse of p embeds the target base into this source stage with all
its complete unary values unchanged.

The already certified all-closed-base functional extension theorem
realizes T in the target limit over that target base. The stage T
and the image of the response constitute a new finite closed functional
partial isomorphism extending p, with k in its source.

The new target is automatically C-closed by complete value equality;
therefore it is globally strong. The source is a genuine globally
strong finite stage. We use the *same* embedding for graph, unary
values and pointwise extension.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteStrongPartialIso
namespace FiniteClosedFunctionalPartialIso

open FiniteFunctionalNatStage

/-- Every finite closed complete-functional partial automorphism of the
actual countable C₀ limit extends to cover an arbitrary prescribed
new source vertex. Both the source and the target of the extended
partial map remain finite, globally strong and C-closed. -/
theorem fairLimit_forth
    (p : FiniteClosedFunctionalPartialIso
      fairGraphStages.limitGraph fairGraphStages.limitGraph
      fairUnaryStages.limitValue fairUnaryStages.limitValue)
    (k : ℕ) :
    ∃ q : FiniteClosedFunctionalPartialIso
      fairGraphStages.limitGraph fairGraphStages.limitGraph
      fairUnaryStages.limitValue fairUnaryStages.limitValue,
      Extends p q ∧ k ∈ q.graph.source := by
  classical
  let N : GraphOn ℕ := fairGraphStages.limitGraph
  let C : ℕ → Finset ℕ := fairUnaryStages.limitValue
  obtain ⟨n, hCover⟩ :=
    fairCoherentC0Stages.finite_stage_cover
      (insert k p.graph.source)
  have hOld : p.graph.source ⊆ fairGraphStages.stage n := by
    intro x hx
    exact hCover (Finset.mem_insert_of_mem hx)
  let T := {v : ℕ // v ∈ fairGraphStages.stage n}
  let R := {v : ℕ // v ∈ p.graph.target}
  let G : GraphOn T :=
    N.pullback (Subtype.val : T → ℕ)
  let i : R → T :=
    inverseStageBaseMap p (fairGraphStages.stage n) hOld
  have hi : Function.Injective i :=
    inverseStageBaseMap_injective p (fairGraphStages.stage n) hOld
  obtain ⟨m, κ, hSteps, hStageValues⟩ :=
    fairLimitCanonicalStages n
  have hSparse : G.IsTwoSparse (Finset.univ : Finset T) :=
    FiniteC0.canonicalStages_literalStage_twoSparse
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages n
  have hAdj : ∀ a b : R,
      N.adj a.val b.val ↔ G.adj (i a) (i b) :=
    inverseStageBaseMap_induced p (fairGraphStages.stage n) hOld
  have hBaseValue : ∀ a : R,
      FiniteC0.canonicalValue G κ (i a) =
        (FiniteC0.namedClosedBaseValue C p.graph.target a).image i := by
    intro a
    exact inverseStageBaseMap_completeValues
      p (fairGraphStages.stage n) hOld κ hStageValues a
  obtain ⟨h, hh, hGraph, hFull, hFix⟩ :=
    fairLimit_hasFunctionalExtension_over_anyClosedBase
      p.graph.target p.targetClosed
      G κ hSteps hSparse i hi hAdj hBaseValue
  let t : Finset ℕ := (Finset.univ : Finset T).image h
  let e : T ≃ {v : ℕ // v ∈ t} :=
    FiniteC0.imageCarrierEquiv h hh
  have hSourceStrong : N.toPredimension.IsGloballyStrong
      (fairGraphStages.stage n) :=
    fairGraphStages.stage_global_of_strong_steps
      fairLimitStrongSteps n
  have hTargetClosed : N.IsClosedUnderValues C t :=
    FiniteC0.fullFunctionalImage_closed
      N C (FiniteC0.canonicalValue G κ) h hFull
  have hTargetStrong : N.toPredimension.IsGloballyStrong t :=
    FiniteC0.canonicalStages_fullFunctionalImage_globalStrong
      N C fairGraphStages.stage
      fairCoherentC0Stages.finite_stage_cover
      fairLimitCanonicalStages
      (FiniteC0.canonicalValue G κ) h hFull
  have hSourceClosed :
      N.IsClosedUnderValues C (fairGraphStages.stage n) := by
    change N.IsClosedUnderValues C
      (Finset.range (fairUnaryStages.size n))
    intro x hx y hy
    exact fairUnaryStages.stage_closed n x hx hy
  let q : FiniteClosedFunctionalPartialIso N N C C :=
    { graph :=
        { source := fairGraphStages.stage n
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
            b.val ∈ C a.val ↔
              b ∈ FiniteC0.canonicalValue G κ a :=
          (FiniteC0.fullFunctionalImage_mem_iff
            C (FiniteC0.canonicalValue G κ)
            (Subtype.val : T → ℕ) Subtype.val_injective
            hStageValues a b)
        have hTargetMembership :
            h b ∈ C (h a) ↔
              b ∈ FiniteC0.canonicalValue G κ a :=
          FiniteC0.fullFunctionalImage_mem_iff
            C (FiniteC0.canonicalValue G κ)
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
