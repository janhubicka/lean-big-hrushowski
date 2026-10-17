import BigHrushovski.CFFiniteGenericity
import BigHrushovski.CFRealGrowthRestriction

/-!
# Full finite C_F extensions under the published real-growth assumptions

The finite birth-graph extension theorem needs a numerical bound K
satisfying F_nat(m) ≤ 2(k+1) → m ≤ K(k). The exact discrete
generalized inverse of the restriction of an unbounded monotone
real function supplies this bound. No separately postulated K
is needed in the final finite extension statement.

This module also introduces the canonical choice of cardinal growth
and its inverse once, rather than duplicating the analytic
specialization in each local response theorem.
-/

namespace BigHrushovski

namespace CFGrowthNumerics

/-- Restrict real growth to integer vertex cardinalities. -/
abbrev cardinalGrowth (F : ℝ → ℝ) : ℕ → ℝ :=
  fun n => F (n : ℝ)

/-- Canonical integer inverse size bound supplied by real growth. -/
noncomputable def cardinalGrowthBound
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) : ℕ → ℕ :=
  growthInverseSize (cardinalGrowth F)
    (realGrowth_nat_unbounded F hMono hUnbounded)

/-- The exact numerical premise of the tagged extension catalogue,
obtained solely from F(0)=0, monotonicity and unboundedness. -/
theorem cardinalGrowth_inverse
    (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) :
    ∀ k m : ℕ,
      cardinalGrowth F m ≤ 2 * (((k + 1 : ℕ) : ℝ)) →
        m ≤ cardinalGrowthBound F hMono hUnbounded k := by
  intro k m hm
  let Fnat : ℕ → ℝ := cardinalGrowth F
  have hZeroNat : Fnat 0 = 0 := by
    simpa [Fnat, cardinalGrowth] using hZero
  exact (growthInverseSize_iff Fnat hZeroNat
    (realGrowth_nat_monotone F hMono)
    (realGrowth_nat_unbounded F hMono hUnbounded) k m).mp hm

end CFGrowthNumerics

namespace CFCoherentTower

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- An actual birth vertex for the finite C_F construction with
the canonical numerical bound derived from the real growth F. -/
abbrev RealBirthVertex
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) : Type :=
  Vertex (CFGrowthNumerics.cardinalGrowth F)
    (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)

/-- The corresponding countable birth graph, with no freely
chosen numerical catalogue cutoff. -/
noncomputable abbrev realCountableGraph
    (F : ℝ → ℝ) (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x) :
    GraphOn (RealBirthVertex F hMono hUnbounded) :=
  countableGraph (CFGrowthNumerics.cardinalGrowth F)
    (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)

/-- Finite prescribed-base extension for the actual real growth
function: any finite strict d-closed inclusion of a finite C_F
graph admits an induced globally d-closed copy in the countable
tagged graph, fixing the prescribed base embedding pointwise.

Unlike the discrete theorem, this states no external K-inverse
hypothesis. Only the paper's real growth and finite class
membership hypotheses remain explicit. -/
theorem finiteRealDClosedInterval_globalResponse
    (G : GraphOn V) (F : ℝ → ℝ)
    (hZero : F 0 = 0)
    (hMono : Monotone F)
    (hUnbounded : ∀ t : ℝ, ∃ x : ℝ, t < F x)
    (hGrowth : G.IsGrowthSparse
      (CFGrowthNumerics.cardinalGrowth F) Finset.univ)
    (a b : Finset V)
    (hab : G.toPredimension.IsDClosed a b)
    (e : {v : V // v ∈ a} → RealBirthVertex F hMono hUnbounded)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : {v : V // v ∈ a},
      G.adj x.val y.val ↔
        (realCountableGraph F hMono hUnbounded).adj (e x) (e y))
    (heClosed : (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
      ((Finset.univ : Finset {v : V // v ∈ a}).image e)) :
    ∃ g : {v : V // v ∈ b} → RealBirthVertex F hMono hUnbounded,
      Function.Injective g ∧
      (∀ x : {v : V // v ∈ a},
        g ⟨x.val, hab.1 x.property⟩ = e x) ∧
      (∀ x y : {v : V // v ∈ b},
        G.adj x.val y.val ↔
          (realCountableGraph F hMono hUnbounded).adj (g x) (g y)) ∧
      (realCountableGraph F hMono hUnbounded).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset {v : V // v ∈ b}).image g) := by
  exact finiteDClosedInterval_globalResponse G
    (CFGrowthNumerics.cardinalGrowth F)
    (CFGrowthNumerics.cardinalGrowthBound F hMono hUnbounded)
    (CFGrowthNumerics.cardinalGrowth_inverse F hZero hMono hUnbounded)
    hGrowth a b hab e heInj heAdj heClosed

end CFCoherentTower
end BigHrushovski
