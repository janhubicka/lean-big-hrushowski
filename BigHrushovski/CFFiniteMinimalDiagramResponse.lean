import BigHrushovski.CFArbitraryMinimalResponse
import BigHrushovski.CFPrescribedSourceLift
import BigHrushovski.CFLocalSplitGraph

/-!
# Realize an arbitrary finite minimal C_F diagram over its prescribed image

The preceding theorem responds to a minimal extension already
presented on a disjoint old/new carrier S ⊕ B. Here the source
and target are given as *literal finite vertex subsets* a,b of
an arbitrary finite graph G; the finite vertex set b is
disjoint from the old source a.

The complete induced graph on a ∪ b is transported to the
literal split carrier a_subtype ⊕ b_subtype. The existing
minimal-step image theorem preserves strict minimality,
and the growth-class image theorem preserves every induced
edge and nonedge. A globally strictly d-closed prescribed
embedding of the source into the countable C_F birth graph
is lifted pointwise into an actual finite tagged stage.
The certified arbitrary minimal-response theorem then
attaches the correct new tagged block over the literal
canonical support and gives an induced globally d-closed
copy of the full extension.

The target is written on a_subtype ⊕ Fin(card b), with the
new vertices in their inherited order; no unrelated copy
of the old source is substituted. No countable extension
property is assumed. The remaining step is to transport
this finite response back across the canonical equivalence
with a general finite labelled target, then iterate the
already certified finite minimal-step decomposition.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFLocalCatalogue

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A finite growth-class minimal strict d-closed extension
a <_d a ∪ b admits a globally strictly d-closed induced
response over a *prescribed* old source embedding into the
countable birth graph, with old vertices fixed pointwise.

The new block is enumerated increasingly, as in the
manuscript. Only the exact numerical inverse-size
domination property remains an explicit assumption. -/
theorem finiteMinimalDiagram_globalResponse
    (G : GraphOn V)
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k m : ℕ,
      F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k)
    (a b : Finset V)
    (hDisjoint : Disjoint a b)
    (hMinimal : G.toPredimension.IsMinimalDClosedStep a (a ∪ b))
    (hGrowth : G.IsGrowthSparse F (a ∪ b))
    (e : OldCarrier V a → Vertex F K)
    (he : Function.Injective e)
    (heAdj : ∀ x y : OldCarrier V a,
      G.adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset (OldCarrier V a)).image e)) :
    let S := OldCarrier V a
    let B := FreshCarrier V b
    let H := splitGraph G a b
    ∃ g : Sum S (Fin (Fintype.card B)) → Vertex F K,
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) = e x) ∧
      (∀ x y : Sum S (Fin (Fintype.card B)),
        (H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (increasingNewBlock (B := B)).toEquiv)).adj x y ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin (Fintype.card B)))).image g) := by
  classical
  dsimp only
  let S := OldCarrier V a
  let B := FreshCarrier V b
  let H : GraphOn (Sum S B) := splitGraph G a b
  let A : GraphOn S := G.pullback Subtype.val
  obtain ⟨n, f, hf, hfAdj, hfBirth, hfClosed⟩ :=
    prescribedClosedSource_liftToStage F K A e he
      (fun x y => heAdj x y) heClosed
  have hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage F K n).graph.adj (f x) (f y) := by
    intro x y
    change G.adj x.val y.val ↔
      (stage F K n).graph.adj (f x) (f y)
    exact hfAdj x y
  have hMin : H.toPredimension.IsMinimalDClosedStep
      (actualOld S B) Finset.univ :=
    splitGraph_minimal G a b hDisjoint hMinimal
  have hGrowthLocal : H.IsGrowthSparse F Finset.univ :=
    (splitGraph_growthSparse_iff G F a b hDisjoint).mpr hGrowth
  obtain ⟨g, hgInj, hgOld, hgAdj, hgClosed⟩ :=
    arbitraryMinimalCF_globalResponse F K hInverse n
      H hMin hGrowthLocal f hf hOld hfClosed
  refine ⟨g, hgInj, ?_, ?_, hgClosed⟩
  · intro x
    exact (hgOld x).trans (hfBirth x)
  · intro x y
    exact hgAdj x y

end CFCoherentTower
end BigHrushovski
