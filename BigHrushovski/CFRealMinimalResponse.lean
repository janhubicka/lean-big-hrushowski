import BigHrushovski.CFArbitraryMinimalResponse
import BigHrushovski.CFRealGrowthRestriction

/-!
# Minimal C_F responses under the published real-growth assumptions

The tagged C_F construction uses a growth function on nonnegative
real arguments, evaluated at integer vertex cardinalities.
The independently verified numerical theorem constructs the
exact integer generalized inverse from monotonicity,
unboundedness, and F(0)=0. The complete arbitrary minimal
response therefore needs no separately postulated K-bound.

For the integer restriction F_nat(k)=F(k), let K(k) be the
largest integer N with F_nat(N)<=2(k+1). Given a minimal
strict d-closed finite growth-class extension of an old
stage, the actual tagged construction attaches its complete
induced copy over the prescribed old source, with globally
strictly d-closed image.

This is a one-step result. The remaining full genericity
statement requires transporting general labelled finite
minimal diagrams into a split old/new representation and
iterating the certified minimal-step decomposition.
-/

namespace BigHrushovski

namespace CFGrowthNumerics

/-- Evaluate the published real growth function at finite vertex
cardinalities. This is the only growth predicate used by finite graphs. -/
abbrev cardinalGrowth (F : ℝ → ℝ) : ℕ → ℝ :=
  fun k => F (k : ℝ)

/-- Exact cardinality bound determined by the paper's real growth
function, with no separately chosen numerical size parameter. -/
noncomputable def cardinalGrowthBound
    (F : ℝ → ℝ)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) : ℕ → ℕ :=
  growthInverseSize (cardinalGrowth F)
    (realGrowth_nat_unbounded F hMono hUnbounded)

end CFGrowthNumerics

namespace CFCoherentTower

variable {S B : Type*} [Fintype S] [DecidableEq S]
variable [Fintype B] [DecidableEq B] [LinearOrder B]

/-- The named global minimal one-block response under the
real-growth hypotheses of the manuscript. The size bound is
defined by the exact generalized inverse of cardinal growth. -/
theorem arbitraryMinimalRealCF_globalResponse
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (n : ℕ)
    (H : GraphOn (Sum S B))
    (hMin : H.toPredimension.IsMinimalDClosedStep
      (CFLocalCatalogue.actualOld S B) Finset.univ)
    (hGrowth : H.IsGrowthSparse
      (CFGrowthNumerics.cardinalGrowth F) Finset.univ)
    (f : S → (stage (CFGrowthNumerics.cardinalGrowth F)
      (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
      n).carrier)
    (hf : Function.Injective f)
    (hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
          n).graph.adj (f x) (f y))
    (hClosed : (stage (CFGrowthNumerics.cardinalGrowth F)
      (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
      n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ) :
    ∃ g : Sum S (Fin (Fintype.card B)) →
        Vertex (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded),
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) =
        toVertex (CFGrowthNumerics.cardinalGrowth F)
          (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
          n (f x)) ∧
      (∀ x y : Sum S (Fin (Fintype.card B)),
        (H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (CFLocalCatalogue.increasingNewBlock (B := B)).toEquiv)).adj x y ↔
          (countableGraph (CFGrowthNumerics.cardinalGrowth F)
            (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)).adj
            (g x) (g y)) ∧
      (countableGraph (CFGrowthNumerics.cardinalGrowth F)
        (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded))
        .toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin (Fintype.card B)))).image g) := by
  classical
  let Fnat : ℕ → ℝ := CFGrowthNumerics.cardinalGrowth F
  let huNat := CFGrowthNumerics.realGrowth_nat_unbounded
    F hMono hUnbounded
  let K : ℕ → ℕ :=
    CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded
  have hInverse : ∀ k m : ℕ,
      Fnat m ≤ 2 * (((k + 1 : ℕ) : ℝ)) → m ≤ K k := by
    intro k m h
    exact (CFGrowthNumerics.growthInverseSize_iff Fnat
      (by simpa [Fnat, CFGrowthNumerics.cardinalGrowth] using hZero)
      (CFGrowthNumerics.realGrowth_nat_monotone F hMono)
      huNat k m).mp h
  exact arbitraryMinimalCF_globalResponse Fnat K hInverse
    n H hMin hGrowth f hf hOld hClosed

end CFCoherentTower
end BigHrushovski
