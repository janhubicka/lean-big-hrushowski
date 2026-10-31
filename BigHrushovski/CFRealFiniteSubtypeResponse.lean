import BigHrushovski.CFDClosedFiniteSubtype
import BigHrushovski.CFRealFiniteGenericity

/-!
# Full finite C_F response for literal intervals of a countable source

The existing arbitrary-finite real-growth theorem is parametrized by a
finite linearly ordered vertex type. In the countable recognition
argument the source is a graph on ℕ and the prescribed interval is
an arbitrary finite inclusion a ≤d b.

We apply the finite theorem to the *literal finite induced subtype*
{v : ℕ // v∈b}, rather than choosing a new Fin numbering. A
canonical equivalence between the old subtype of a and the
corresponding filtered subtype of b carries the prescribed old
embedding to the exact finite-response interface. Both the
resulting old map and the full target interval retain their
original labels, induced graph and global strict d-closedness.

The target is still the canonical birth-labelled graph. Moving that
target to a Nat presentation and deriving the actual generic
identification is a separate countable-carrier theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFDClosedFiniteSubtype CFGrowthNumerics

/-- Every literal finite d-closed growth-class interval a ≤d b in
a countable source graph has its complete prescribed-base response in
the real-growth canonical birth graph. No genericity of the source
graph is assumed. -/
theorem finiteRealDClosedNatInterval_globalResponse
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (M : GraphOn ℕ)
    (a b : Finset ℕ)
    (hab : M.toPredimension.IsDClosed a b)
    (hGrowth : M.IsGrowthSparse (cardinalGrowth F) b)
    (e : {v : ℕ // v ∈ a} → RealBirthVertex F hMono hUnbounded)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : {v : ℕ // v ∈ a},
      M.adj x.val y.val ↔
        (realCountableGraph F hMono hUnbounded).adj (e x) (e y))
    (heClosed : (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset {v : ℕ // v ∈ a}).image e)) :
    ∃ g : {v : ℕ // v ∈ b} → RealBirthVertex F hMono hUnbounded,
      Function.Injective g ∧
      (∀ x : {v : ℕ // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x) ∧
      (∀ x y : {v : ℕ // v ∈ b},
        M.adj x.val y.val ↔
          (realCountableGraph F hMono hUnbounded).adj (g x) (g y)) ∧
      (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : ℕ // v ∈ b}).image g) := by
  classical
  let V := Carrier b
  let G : GraphOn V := graph M b
  let P : Finset V := base b a
  have hP : G.toPredimension.IsDClosed P (Finset.univ : Finset V) :=
    (dClosed_iff M a b hab.1).mp hab
  have hGrowthFinite :
      G.IsGrowthSparse (cardinalGrowth F)
        (Finset.univ : Finset V) :=
    (growthSparse_iff M (cardinalGrowth F) b).mp hGrowth
  let E : {v : ℕ // v ∈ a} ≃ {v : V // v ∈ P} :=
    { toFun := fun x =>
        ⟨⟨x.val, hab.1 x.property⟩, by
          change (⟨x.val, hab.1 x.property⟩ : V) ∈
            Finset.univ.filter (fun y : V => y.val ∈ a)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun y =>
        ⟨y.val.val, by
          have hy : y.val ∈
            Finset.univ.filter (fun z : V => z.val ∈ a) :=
            y.property
          exact (Finset.mem_filter.mp hy).2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  let f : {v : V // v ∈ P} → RealBirthVertex F hMono hUnbounded :=
    fun y => e (E.symm y)
  have hfInj : Function.Injective f :=
    heInj.comp E.symm.injective
  have hfAdj : ∀ x y : {v : V // v ∈ P},
      G.adj x.val y.val ↔
        (realCountableGraph F hMono hUnbounded).adj (f x) (f y) := by
    intro x y
    simpa [f, E, G, graph] using heAdj (E.symm x) (E.symm y)
  have hfImage :
      ((Finset.univ : Finset {v : V // v ∈ P}).image f) =
      ((Finset.univ : Finset {v : ℕ // v ∈ a}).image e) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr
        ⟨E.symm x, Finset.mem_univ _, hx⟩
    · intro hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨E x, Finset.mem_univ _, ?_⟩
      change e (E.symm (E x)) = w
      simpa using hx
  have hfClosed :
      (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ P}).image f) := by
    rw [hfImage]
    exact heClosed
  obtain ⟨g0, hg0Inj, hg0Old, hg0Adj, hg0Closed⟩ :=
    finiteRealDClosedInterval_globalResponse
      G F hZero hMono hUnbounded hGrowthFinite
      P Finset.univ hP f hfInj hfAdj hfClosed
  let g : {v : ℕ // v ∈ b} → RealBirthVertex F hMono hUnbounded :=
    fun x => g0 ⟨x, Finset.mem_univ _⟩
  have hgInj : Function.Injective g := by
    intro x y hxy
    have hxy' :
        (⟨x, Finset.mem_univ _⟩ :
          {v : V // v ∈ (Finset.univ : Finset V)}) =
        ⟨y, Finset.mem_univ _⟩ := hg0Inj hxy
    exact congrArg Subtype.val hxy'
  have hgOld :
      ∀ x : {v : ℕ // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x := by
    intro x
    have h := hg0Old (E x)
    simpa [g, f, E] using h
  have hgAdj : ∀ x y : {v : ℕ // v ∈ b},
      M.adj x.val y.val ↔
        (realCountableGraph F hMono hUnbounded).adj (g x) (g y) := by
    intro x y
    simpa [g, G, graph] using
      (hg0Adj (⟨x, Finset.mem_univ _⟩ :
          {v : V // v ∈ (Finset.univ : Finset V)})
        ⟨y, Finset.mem_univ _⟩)
  have hgImage :
      ((Finset.univ : Finset {v : ℕ // v ∈ b}).image g) =
      ((Finset.univ :
          Finset {v : V // v ∈ (Finset.univ : Finset V)}).image g0) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr
        ⟨⟨x, Finset.mem_univ _⟩, Finset.mem_univ _, hx⟩
    · intro hw
      obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr
        ⟨x.val, Finset.mem_univ _, hx⟩
  refine ⟨g, hgInj, hgOld, hgAdj, ?_⟩
  rw [hgImage]
  exact hg0Closed

end CFCoherentTower
end BigHrushovski
