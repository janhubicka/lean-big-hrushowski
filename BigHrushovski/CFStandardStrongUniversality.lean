import BigHrushovski.CFStandardFraisseExtension

/-!
# Strong universality from the ordinary finite extension property

The finite strong universality argument does not depend on the
canonical C_F construction. If the empty graph is globally strictly
d-closed in a target and is strictly d-closed in the finite source,
the standard prescribed-base strong extension property embeds the
whole source over the uniquely prescribed empty map.

This separates the elementary empty-base argument from the
birth-labelled graph and avoids repeating finite-image calculations
for each strong Fraisse-limit presentation.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

variable {V : Type*} [DecidableEq V]

/-- A graph with the ordinary strong extension property and globally
strictly d-closed empty set contains a globally strictly d-closed
induced copy of any finite growth-class graph with strictly
d-closed empty base.

No age, covering chain, countability, numbering or free-amalgamation
assumption on the target is needed. The source map is the unique
map from the literally empty finite subtype. -/
theorem finiteStrongUniversality_of_standardExtensions
    (F : ℕ → ℝ) (G : GraphOn V)
    (hExtensions : HasStandardFiniteDClosedExtensions F G)
    (hEmptyG : G.toPredimension.IsGloballyDClosed ∅)
    (W : Type) [Fintype W] [DecidableEq W]
    (B : GraphOn W)
    (hGrowth : B.IsGrowthSparse F (Finset.univ : Finset W))
    (hEmptyB : B.toPredimension.IsDClosed
      (∅ : Finset W) Finset.univ) :
    ∃ g : W → V,
      Function.Injective g ∧
      (∀ x y : W, B.adj x y ↔ G.adj (g x) (g y)) ∧
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset W).image g) := by
  classical
  have emptyElim (x : {w : W // w ∈ (∅ : Finset W)}) : False :=
    Finset.notMem_empty x.val x.property
  let e : {w : W // w ∈ (∅ : Finset W)} → V :=
    fun x => False.elim (emptyElim x)
  have heInj : Function.Injective e := by
    intro x y _
    exact False.elim (emptyElim x)
  have heAdj : ∀ x y : {w : W // w ∈ (∅ : Finset W)},
      B.adj x.val y.val ↔ G.adj (e x) (e y) := by
    intro x y
    exact False.elim (emptyElim x)
  have hImage :
      ((Finset.univ : Finset {w : W // w ∈ (∅ : Finset W)}).image e) =
        (∅ : Finset V) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, _, _⟩ := Finset.mem_image.mp hv
      exact False.elim (emptyElim x)
    · simp
  have heClosed :
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {w : W // w ∈ (∅ : Finset W)}).image e) := by
    rw [hImage]
    exact hEmptyG
  obtain ⟨g, hgInj, _, hgAdj, hgClosed⟩ :=
    hExtensions W B ∅ hGrowth hEmptyB e heInj heAdj heClosed
  exact ⟨g, hgInj, hgAdj, hgClosed⟩

end CFDClosedBackAndForth
end BigHrushovski
