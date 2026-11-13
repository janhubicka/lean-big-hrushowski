import BigHrushovski.C0FunctionalAllClosedBaseExtension

/-!
# Track A: universality of the constructed functional C₀ limit

The actual countable C₀ functional limit has the extension property
over every finite closed base. Taking the empty closed base gives
universality for all finite canonical C₀ structures.

The resulting map is a single induced injective graph embedding
which also preserves the *entire* canonical set-valued unary
operation. Neither homogeneity nor an arbitrary canonical order on
components is invoked.

This corollary is logically independent of the still-pending finite
back-and-forth homogeneity theorems.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Every finite canonical two-sparse C₀ structure embeds into the
actual constructed countable functional C₀ limit, preserving and
reflecting graph adjacency and transporting complete unary values.

The empty-base case of the already certified arbitrary-closed-base
extension theorem yields this with no new amalgamation construction.
-/
theorem fairLimit_universalForFiniteFunctionalC0
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B)
    {m : ℕ} (κ : B → Fin m)
    (hSteps : ∀ k : ℕ, k < m →
      FiniteC0.oldStage κ k =
        FiniteC0.oldStage κ (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k)
        (FiniteC0.oldStage κ (k + 1)))
    (hSparse : H.IsTwoSparse (Finset.univ : Finset B)) :
    ∃ f : B → ℕ,
      Function.Injective f ∧
      (∀ u v : B,
        H.adj u v ↔ fairGraphStages.limitGraph.adj (f u) (f v)) ∧
      (∀ u : B,
        fairUnaryStages.limitValue (f u) =
          (FiniteC0.canonicalValue H κ u).image f) := by
  classical
  let s : Finset ℕ := ∅
  have hNo (a : {v : ℕ // v ∈ s}) : False := by
    have ha : a.val ∈ (∅ : Finset ℕ) := a.property
    simpa using ha
  have hClosed :
      fairGraphStages.limitGraph.IsClosedUnderValues
        fairUnaryStages.limitValue s := by
    intro x hx
    have hxf : x ∈ (∅ : Finset ℕ) := hx
    simp at hxf
  let j : {v : ℕ // v ∈ s} → B := fun a => (hNo a).elim
  have hj : Function.Injective j := by
    intro a b _
    exact (hNo a).elim
  have hAdj : ∀ a b : {v : ℕ // v ∈ s},
      fairGraphStages.limitGraph.adj a.val b.val ↔
        H.adj (j a) (j b) := by
    intro a b
    exact (hNo a).elim
  have hValue : ∀ a : {v : ℕ // v ∈ s},
      FiniteC0.canonicalValue H κ (j a) =
        (FiniteC0.namedClosedBaseValue
          fairUnaryStages.limitValue s a).image j := by
    intro a
    exact (hNo a).elim
  obtain ⟨f, hf, hGraph, hFull, _⟩ :=
    fairLimit_hasFunctionalExtension_over_anyClosedBase
      s hClosed H κ hSteps hSparse
      j hj hAdj hValue
  exact ⟨f, hf, hGraph, hFull⟩

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
