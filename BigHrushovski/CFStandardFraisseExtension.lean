import BigHrushovski.CFStrongFraisseLimitPresentation
import BigHrushovski.CFDClosedFiniteSubtype

/-!
# The ordinary finite Fraisse extension property implies the Nat-code API

The introduction of the manuscript uses the usual extension
property: for every finite C_F-member B and every d-closed
substructure A ≤_d B, an already embedded strong copy of A
extends to a strong induced copy of B.

Our countable Lean recognition theorem uses a finite inclusion
a ≤_d b in an arbitrary graph on ℕ. This file proves the needed
implication from the ordinary finite-source formulation to that
Nat-labelled interval formulation, using the literal finite
induced subtype of b. No arbitrary total embedding of an
infinite source or a silently renamed old value is used.

Only the forward implication needed for identifying M_F is
claimed. We do not state a converse without independently
checking the finite coding in that direction.
-/

namespace BigHrushovski
namespace CFDClosedBackAndForth

variable {V : Type*} [DecidableEq V]

/-- The ordinary finite strong Fraisse extension property
on a graph G with its original vertex carrier V.

The finite extension B has any finite carrier W, and A is
the literal d-closed subset of its vertices. The old map
is an induced embedding with globally strictly d-closed
image; the extension preserves that old map pointwise,
remains induced, and has globally strictly d-closed image.
All finite graphs are considered only if their entire
endpoint is in the restricted growth class C_F. -/
def HasStandardFiniteDClosedExtensions
    (F : ℕ → ℝ) (G : GraphOn V) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W]
    (B : GraphOn W) (a : Finset W),
    B.IsGrowthSparse F (Finset.univ : Finset W) →
    B.toPredimension.IsDClosed a Finset.univ →
    ∀ (f : {w : W // w ∈ a} → V),
      Function.Injective f →
      (∀ x y : {w : W // w ∈ a},
        B.adj x.val y.val ↔ G.adj (f x) (f y)) →
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {w : W // w ∈ a}).image f) →
      ∃ g : W → V,
        Function.Injective g ∧
        (∀ x : {w : W // w ∈ a}, g x.val = f x) ∧
        (∀ x y : W,
          B.adj x y ↔ G.adj (g x) (g y)) ∧
        G.toPredimension.IsGloballyDClosed
          ((Finset.univ : Finset W).image g)

/-- The standard finite-source strong extension property
implies the native-carrier Nat-interval response API.

For a source a ≤_d b inside an arbitrary graph on ℕ, use
the literal induced finite carrier {v // v ∈ b} and its
literal old subset. All class-membership and strict
closure facts transfer exactly along the subtype
embedding, and the prescribed old map survives unchanged. -/
theorem HasStandardFiniteDClosedExtensions.toNatIntervals
    (F : ℕ → ℝ) (G : GraphOn V)
    (hStandard : HasStandardFiniteDClosedExtensions F G) :
    HasFiniteDClosedResponsesOn F G := by
  classical
  intro M a b hGrowth hab e heInj heAdj heClosed
  let W := CFDClosedFiniteSubtype.Carrier b
  let B : GraphOn W := CFDClosedFiniteSubtype.graph M b
  let P : Finset W := CFDClosedFiniteSubtype.base b a
  have hGrowthW :
      B.IsGrowthSparse F (Finset.univ : Finset W) :=
    (CFDClosedFiniteSubtype.growthSparse_iff M F b).mp hGrowth
  have hPW :
      B.toPredimension.IsDClosed P (Finset.univ : Finset W) :=
    (CFDClosedFiniteSubtype.dClosed_iff M a b hab.1).mp hab
  let E : {v : ℕ // v ∈ a} ≃ {v : W // v ∈ P} :=
    { toFun := fun x =>
        ⟨⟨x.val, hab.1 x.property⟩, by
          change (⟨x.val, hab.1 x.property⟩ : W) ∈
            Finset.univ.filter (fun y : W => y.val ∈ a)
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, x.property⟩⟩
      invFun := fun y =>
        ⟨y.val.val, by
          have hy : y.val ∈
            Finset.univ.filter (fun z : W => z.val ∈ a) :=
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
  let fW : {w : W // w ∈ P} → V :=
    fun y => e (E.symm y)
  have hfWInj : Function.Injective fW :=
    heInj.comp E.symm.injective
  have hfWAdj : ∀ x y : {w : W // w ∈ P},
      B.adj x.val y.val ↔ G.adj (fW x) (fW y) := by
    intro x y
    change M.adj x.val.val y.val.val ↔
      G.adj (e (E.symm x)) (e (E.symm y))
    exact heAdj (E.symm x) (E.symm y)
  have hOldImage :
      ((Finset.univ : Finset {w : W // w ∈ P}).image fW) =
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
  have hfWClosed :
      G.toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {w : W // w ∈ P}).image fW) := by
    rw [hOldImage]
    exact heClosed
  obtain ⟨gW, hgWInj, hgWOld, hgWAdj, hgWClosed⟩ :=
    hStandard W B P hGrowthW hPW fW
      hfWInj hfWAdj hfWClosed
  let g : {v : ℕ // v ∈ b} → V := fun x => gW x
  have hgInj : Function.Injective g := hgWInj
  have hgOld :
      ∀ x : {v : ℕ // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x := by
    intro x
    have h := hgWOld (E x)
    simpa [g, fW, E] using h
  have hgAdj : ∀ x y : {v : ℕ // v ∈ b},
      M.adj x.val y.val ↔ G.adj (g x) (g y) := by
    intro x y
    change M.adj x.val y.val ↔ G.adj (gW x) (gW y)
    exact hgWAdj x y
  refine ⟨g, hgInj, hgOld, hgAdj, ?_⟩
  have hEndpointImage :
      ((Finset.univ : Finset {v : ℕ // v ∈ b}).image g) =
        ((Finset.univ : Finset W).image gW) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  rw [hEndpointImage]
  exact hgWClosed

/-- Exactly the manuscript's ordinary finite-source strong
Fraisse-limit presentation on an arbitrary countably infinite
vertex carrier. The covering chain supplies global finite
d-closed covers, while the standard finite source extension
property is transported by the proved literal subtype map. -/
structure StandardStrongFraisseLimitPresentation
    (F : ℕ → ℝ) (G : GraphOn V) where
  enumerate : ℕ ≃ V
  age : ∀ s : Finset V, F s.card ≤ (G.predim s : ℝ)
  chain : Predimension.DClosedChain G.toPredimension
  standard_extensions : HasStandardFiniteDClosedExtensions F G

/-- A countable strong Fraisse limit defined with arbitrary
finite source graphs and the usual strong embedding notion
satisfies the native recognition interface, with no extra
genericity hypothesis. -/
def StandardStrongFraisseLimitPresentation.toNative
    (F : ℕ → ℝ) (G : GraphOn V)
    (h : StandardStrongFraisseLimitPresentation F G) :
    StrongFraisseLimitPresentation F G where
  enumerate := h.enumerate
  age := h.age
  chain := h.chain
  finite_extensions :=
    h.standard_extensions.toNatIntervals F G

/-- Identification of the original C_F birth graph with a
countable strong Fraisse limit specified by the exact
usual finite-source extension property, rather than any
Nat-coded extension assumption. -/
theorem realBirth_iso_standardStrongFraisseLimit
    (F : ℝ → ℝ) (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hFree : CFCoherentTower.HasFiniteClassDClosedFreeJoins
      (CFGrowthNumerics.cardinalGrowth F))
    (hRequests : ∀ n : ℕ,
      Nonempty (CFStageCatalogue.StageRequest
        (CFCoherentTower.stage
          (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) n).graph
        (CFStageCatalogue.GrowthAllowedLocal
          (CFGrowthNumerics.cardinalGrowth F))
        (fun P =>
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded) P.card)))
    (hEmptyClass : HasClassDClosedEmpty (CFGrowthNumerics.cardinalGrowth F))
    (G : GraphOn V)
    (hG : StandardStrongFraisseLimitPresentation
      (CFGrowthNumerics.cardinalGrowth F) G) :
    ∃ φ : CFCoherentTower.RealBirthVertex F hMono hUnbounded ≃ V,
      ∀ x y : CFCoherentTower.RealBirthVertex F hMono hUnbounded,
        (CFCoherentTower.realCountableGraph F hMono hUnbounded).adj x y ↔
          G.adj (φ x) (φ y) := by
  exact realBirth_iso_strongFraisseLimit F hZero hMono
    hUnbounded hFree hRequests hEmptyClass G
    (hG.toNative (CFGrowthNumerics.cardinalGrowth F) G)

end CFDClosedBackAndForth
end BigHrushovski
