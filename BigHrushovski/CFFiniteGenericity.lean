import BigHrushovski.CFDependentMinimalChain
import BigHrushovski.CFMinimalLiteralIntervalResponse

/-!
# Full finite labelled d-closed extension property for the C_F birth graph

Combine two previously kernel-checked, independent ingredients:
* each minimal strict d-closed step has a complete induced response on
  its *literal* labelled source subtype, fixing the old image pointwise;
* the finite dependent minimal-chain induction composes such responses.

Crucially we assume C_F growth sparsity on the whole finite *source*
graph. Heredity then supplies it to every minimal interval in the chain.
We do not assume that the individual intervals are d-closed in the
target countable graph: that is the conclusion of each response.

The theorem preserves the original old embedding pointwise and proves
global strict d-closedness of the final induced image. Its numerical
hypothesis is the exact inverse domination used to choose the C_F
stage catalogue. Free-amalgamation closure of the growth class is a
distinct assumption needed for membership of the countable limit;
this finite response does not assert such closure.
-/

namespace BigHrushovski
namespace CFCoherentTower

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Every finite d-closed interval of a finite C_F graph has a
prescribed-base, induced, globally d-closed copy in the actual
countable tagged graph. This is the full *finite extension property*
for the real-growth class once its numerical inverse K is fixed.

There is no assumption that the source copy is an initial segment,
or that the new vertices were already arranged in a split carrier. -/
theorem finiteDClosedInterval_globalResponse
    (G : GraphOn V) (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k m : ℕ,
      F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k)
    (hGrowth : G.IsGrowthSparse F Finset.univ)
    (a b : Finset V)
    (hab : G.toPredimension.IsDClosed a b)
    (e : {v : V // v ∈ a} → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : {v : V // v ∈ a},
      G.adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset {v : V // v ∈ a}).image e)) :
    ∃ g : {v : V // v ∈ b} → Vertex F K,
      Function.Injective g ∧
      (∀ x : {v : V // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x) ∧
      (∀ x y : {v : V // v ∈ b},
        G.adj x.val y.val ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ b}).image g) := by
  classical
  let Valid : (s : Finset V) →
      ({v : V // v ∈ s} → Vertex F K) → Prop :=
    fun s f =>
      Function.Injective f ∧
      (∀ x y : {v : V // v ∈ s},
        G.adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ s}).image f)

  have hLocal : ∀ {s t : Finset V},
      (hst : G.toPredimension.IsMinimalDClosedStep s t) →
      (f : {v : V // v ∈ s} → Vertex F K) →
      Valid s f →
      ∃ g : {v : V // v ∈ t} → Vertex F K,
        Valid t g ∧
        (∀ x : {v : V // v ∈ s},
          g ⟨x.val, hst.1.1 x.property⟩ = f x) := by
    intro s t hst f hf
    dsimp only [Valid] at hf ⊢
    obtain ⟨hfInj, hfAdj, hfClosed⟩ := hf
    have hDisj : Disjoint s (t \ s) := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxFresh
      exact (Finset.mem_sdiff.mp hxFresh).2 hxS
    have hUnion : s ∪ (t \ s) = t := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxS | hxFresh
        · exact hst.1.1 hxS
        · exact (Finset.mem_sdiff.mp hxFresh).1
      · intro hxT
        by_cases hxS : x ∈ s
        · exact Finset.mem_union.mpr (Or.inl hxS)
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_sdiff.mpr ⟨hxT, hxS⟩))
    have hMin :
        G.toPredimension.IsMinimalDClosedStep s (s ∪ (t \ s)) := by
      simpa only [hUnion] using hst
    have hLocalGrowth : G.IsGrowthSparse F (s ∪ (t \ s)) :=
      G.growthSparse_restrict F hGrowth (Finset.subset_univ _)
    obtain ⟨response, hrInj, hrOld, hrAdj, hrClosed⟩ :=
      minimalLiteralInterval_globalResponse G F K hInverse
        s (t \ s) hDisj hMin hLocalGrowth f
        hfInj hfAdj hfClosed

    -- Reinterpret the result on the original literal target subtype.
    let E : {v : V // v ∈ t} ≃
        {v : V // v ∈ s ∪ (t \ s)} :=
      { toFun := fun x => ⟨x.val, by
          rw [hUnion]
          exact x.property⟩
        invFun := fun x => ⟨x.val, by
          have hx : x.val ∈ s ∪ (t \ s) := x.property
          rw [hUnion] at hx
          exact hx⟩
        left_inv := by
          intro x
          apply Subtype.ext
          rfl
        right_inv := by
          intro x
          apply Subtype.ext
          rfl }
    let g : {v : V // v ∈ t} → Vertex F K :=
      fun x => response (E x)
    have hgInj : Function.Injective g :=
      hrInj.comp E.injective
    have hgOld : ∀ x : {v : V // v ∈ s},
        g ⟨x.val, hst.1.1 x.property⟩ = f x := by
      intro x
      have hE : E (⟨x.val, hst.1.1 x.property⟩ :
          {v : V // v ∈ t}) =
          (⟨x.val, Finset.mem_union.mpr (Or.inl x.property)⟩ :
            {v : V // v ∈ s ∪ (t \ s)}) := by
        apply Subtype.ext
        rfl
      change response (E ⟨x.val, hst.1.1 x.property⟩) = f x
      rw [hE]
      exact hrOld x
    have hgAdj : ∀ x y : {v : V // v ∈ t},
        G.adj x.val y.val ↔
          (countableGraph F K).adj (g x) (g y) := by
      intro x y
      change G.adj (E x).val (E y).val ↔
        (countableGraph F K).adj (response (E x)) (response (E y))
      exact hrAdj (E x) (E y)
    have hImage :
        ((Finset.univ : Finset {v : V // v ∈ t}).image g) =
        ((Finset.univ : Finset {v : V // v ∈ s ∪ (t \ s)}).image response) := by
      ext z
      constructor
      · intro hz
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨E x, Finset.mem_univ _, hx⟩
      · intro hz
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
        apply Finset.mem_image.mpr
        refine ⟨E.symm x, Finset.mem_univ _, ?_⟩
        change response (E (E.symm x)) = z
        rw [E.apply_symm_apply]
        exact hx
    have hgClosed : (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ t}).image g) := by
      rw [hImage]
      exact hrClosed
    exact ⟨g, ⟨hgInj, hgAdj, hgClosed⟩, hgOld⟩

  obtain ⟨g, hg, hgOld⟩ :=
    G.toPredimension.lift_dClosed_extension_dependent Valid
      hLocal hab e ⟨heInj, heAdj, heClosed⟩
  exact ⟨g, hg.1, hgOld, hg.2.1, hg.2.2⟩

end CFCoherentTower
end BigHrushovski
