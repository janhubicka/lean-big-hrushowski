import BigHrushovski.CFFiniteIntervalEquiv
import BigHrushovski.CFFiniteMinimalDiagramResponse

/-!
# Respond to a minimal C_F extension on its original finite vertex set

The previous finite C_F response is expressed on the canonical
ordered split carrier a_subtype ⊕ Fin(card b). For a disjoint
minimal extension a <_d a∪b, the ordered split equivalence
maps this carrier *bijectively* onto the original target
vertex set (a∪b)_subtype without changing any old vertex.

Transport the constructed response through the inverse of this
equivalence. The resulting map is an induced injection defined
on precisely the original labelled target vertices, extends
the prescribed embedding of the old subtype pointwise, and
has globally strictly d-closed image in the countable birth
graph. The complete edge and nonedge relation is preserved.

This is the literal one-step extension property. There is no
genericity assumption and no choice of an unrelated
isomorphic old source. The remaining countable extension
property is its finite iteration along a chain of minimal
strict d-closed steps.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFLocalCatalogue

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Every minimal strict d-closed C_F inclusion a <_d a∪b
admits an induced globally d-closed response on the *actual*
finite target vertex type (a∪b)_subtype, over a prescribed
globally d-closed embedding of a. Fresh labels are ordered
as inherited from V and the old vertices are fixed exactly. -/
theorem minimalLiteralInterval_globalResponse
    (G : GraphOn V)
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k m : ℕ,
      F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k)
    (a b : Finset V)
    (hDisj : Disjoint a b)
    (hMin : G.toPredimension.IsMinimalDClosedStep a (a ∪ b))
    (hGrowth : G.IsGrowthSparse F (a ∪ b))
    (e : OldCarrier V a → Vertex F K)
    (he : Function.Injective e)
    (heAdj : ∀ x y : OldCarrier V a,
      G.adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset (OldCarrier V a)).image e)) :
    ∃ g : {v : V // v ∈ a ∪ b} → Vertex F K,
      Function.Injective g ∧
      (∀ x : OldCarrier V a,
        g ⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩ = e x) ∧
      (∀ x y : {v : V // v ∈ a ∪ b},
        G.adj x.val y.val ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ a ∪ b}).image g) := by
  classical
  let S := OldCarrier V a
  let B := FreshCarrier V b
  let H := splitGraph G a b
  let E := orderedSplitUnionEquiv a b hDisj
  obtain ⟨h, hhInj, hhOld, hhAdj, hhClosed⟩ :=
    finiteMinimalDiagram_globalResponse G F K hInverse
      a b hDisj hMin hGrowth e he heAdj heClosed
  let g : {v : V // v ∈ a ∪ b} → Vertex F K :=
    fun x => h (E.symm x)
  have hgInj : Function.Injective g := by
    intro x y hxy
    apply E.symm.injective
    exact hhInj hxy
  have hgOld : ∀ x : S,
      g ⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩ = e x := by
    intro x
    have hx : E (Sum.inl x) =
        (⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩ :
          {v : V // v ∈ a ∪ b}) := by
      apply Subtype.ext
      exact orderedSplitUnionEquiv_old a b hDisj x
    calc
      g ⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩ =
          g (E (Sum.inl x)) := congrArg g hx.symm
      _ = h (Sum.inl x) := by
        change h (E.symm (E (Sum.inl x))) = h (Sum.inl x)
        rw [E.symm_apply_apply]
      _ = e x := hhOld x
  have hgAdj : ∀ x y : {v : V // v ∈ a ∪ b},
      G.adj x.val y.val ↔
        (countableGraph F K).adj (g x) (g y) := by
    intro x y
    let sx := E.symm x
    let sy := E.symm y
    have hx : (E sx).val = x.val :=
      congrArg Subtype.val (E.apply_symm_apply x)
    have hy : (E sy).val = y.val :=
      congrArg Subtype.val (E.apply_symm_apply y)
    have hG : G.adj x.val y.val ↔
        ((H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (increasingNewBlock (B := B)).toEquiv)).adj sx sy) := by
      calc
        G.adj x.val y.val ↔
            G.adj (E sx).val (E sy).val := by rw [hx, hy]
        _ ↔ (H.pullback
            (Equiv.sumCongr (Equiv.refl S)
              (increasingNewBlock (B := B)).toEquiv)).adj sx sy :=
          (orderedSplitUnion_adj_iff G a b hDisj sx sy).symm
    exact hG.trans (hhAdj sx sy)
  have hgImage :
      ((Finset.univ : Finset {v : V // v ∈ a ∪ b}).image g) =
      ((Finset.univ : Finset
        (Sum S (Fin (Fintype.card B)))).image h) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr
        ⟨E.symm x, Finset.mem_univ _, hx⟩
    · intro hw
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨E u, Finset.mem_univ _, ?_⟩
      change h (E.symm (E u)) = w
      rw [E.symm_apply_apply]
      exact hu
  refine ⟨g, hgInj, hgOld, hgAdj, ?_⟩
  rw [hgImage]
  exact hhClosed

end CFCoherentTower
end BigHrushovski
