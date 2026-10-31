import BigHrushovski.CFNonnegativeGrowthAdapter
import BigHrushovski.CFRealFiniteGenericity

/-!
# Complete finite C_F responses from the published growth function

This specializes the already kernel-checked real-growth finite-response
theorem to the manuscript's growth-function type on nonnegative reals
with nonnegative values. The only analytic inputs are F(0)=0,
monotonicity and unboundedness on that nonnegative domain.

The exact cardinal growth inequality uses F(n) itself. The proof
transports it by the equality F_ext(n)=F(n), not by an estimate
or an unmentioned totalization of F to negative arguments.
-/

namespace BigHrushovski
namespace CFGrowthNumerics

/-- The exact growth bound used for graph sizes in the paper. -/
abbrev publishedCardinalGrowth (F : PublishedGrowth) : ℕ → ℝ :=
  fun n => (F ⟨(n : ℝ), Nat.cast_nonneg n⟩).val

/-- The real-domain extension is exactly F at every natural
cardinality, the only arguments used in the finite C_F age. -/
theorem publishedCardinalGrowth_eq (F : PublishedGrowth) :
    publishedCardinalGrowth F =
      cardinalGrowth (extendPublishedGrowth F) := by
  funext n
  exact (extendPublishedGrowth_nat F n).symm

end CFGrowthNumerics

namespace CFCoherentTower

open CFGrowthNumerics

/-- The canonical countable birth carrier for the published,
nonnegative-domain growth function. -/
abbrev PublishedBirthVertex
    (F : PublishedGrowth)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val) :=
  RealBirthVertex (extendPublishedGrowth F)
    (extendPublishedGrowth_monotone F hMono)
    (extendPublishedGrowth_unbounded F hUnbounded)

/-- The actual countable birth graph for the published growth
function, with no separately chosen extension on negative reals. -/
noncomputable abbrev publishedCountableGraph
    (F : PublishedGrowth)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val) :=
  realCountableGraph (extendPublishedGrowth F)
    (extendPublishedGrowth_monotone F hMono)
    (extendPublishedGrowth_unbounded F hUnbounded)

/-- Prescribed-base finite strict d-closed C_F responses under
exactly the published domain/codomain and numerical hypotheses.
All old vertices are fixed literally and every adjacency and
nonadjacency in the target interval is preserved and reflected. -/
theorem finitePublishedDClosedInterval_globalResponse
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : GraphOn V) (F : PublishedGrowth)
    (hZero : (F ⟨(0 : ℝ), le_refl (0 : ℝ)⟩).val = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : NonnegativeReal, t < (F x).val)
    (hGrowth : G.IsGrowthSparse (publishedCardinalGrowth F) Finset.univ)
    (a b : Finset V)
    (hab : G.toPredimension.IsDClosed a b)
    (e : {v : V // v ∈ a} → PublishedBirthVertex F hMono hUnbounded)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : {v : V // v ∈ a},
      G.adj x.val y.val ↔
        (publishedCountableGraph F hMono hUnbounded).adj (e x) (e y))
    (heClosed : (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset {v : V // v ∈ a}).image e)) :
    ∃ g : {v : V // v ∈ b} → PublishedBirthVertex F hMono hUnbounded,
      Function.Injective g ∧
      (∀ x : {v : V // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x) ∧
      (∀ x y : {v : V // v ∈ b},
        G.adj x.val y.val ↔
          (publishedCountableGraph F hMono hUnbounded).adj (g x) (g y)) ∧
      (publishedCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ b}).image g) := by
  have hGrowthReal :
      G.IsGrowthSparse (cardinalGrowth (extendPublishedGrowth F))
        Finset.univ := by
    simpa only [publishedCardinalGrowth_eq F] using hGrowth
  exact finiteRealDClosedInterval_globalResponse G
    (extendPublishedGrowth F)
    (extendPublishedGrowth_zero F hZero)
    (extendPublishedGrowth_monotone F hMono)
    (extendPublishedGrowth_unbounded F hUnbounded)
    hGrowthReal a b hab e heInj heAdj heClosed

end CFCoherentTower
end BigHrushovski
