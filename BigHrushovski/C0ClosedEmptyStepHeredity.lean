import BigHrushovski.C0FiniteCanonicalRestriction

/-!
# Track A: finite closed heredity with genuinely empty component positions

A finite canonical C₀ presentation is indexed by κ : V → Fin n; some
index positions may be unused. Its correct stage hypothesis says that
each consecutive cut is either unchanged or a minimal strong extension.

A closed induced substructure inherits the **same** index, allowing
additional positions to become empty. Every surviving nonempty cut
remains minimal strong in the induced graph, and the complete canonical
unary values are the restrictions of the original complete values.

The proof uses the single-step restriction lemma at genuinely minimal
positions, and literal image equality at empty positions. Thus no
compression of the index or extra enumeration is needed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- Heredity of the **actual** empty-or-minimal canonical finite
component presentation. The previous restriction theorem required
minimality at every slot and could not be applied to unused positions. -/
theorem canonicalValue_restrict_emptyOrMinimalSteps
    (G : GraphOn V) (κ : V → Fin n)
    (hSteps : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k + 1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s) :
    let H := G.pullback
      (Subtype.val : {v : V // v ∈ s} → V)
    let κs := restrictIndex κ s
    ∀ k : ℕ, k < n →
      oldStage κs k = oldStage κs (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage κs k) (oldStage κs (k + 1)) := by
  classical
  change ∀ k : ℕ, k < n →
    oldStage (restrictIndex κ s) k =
      oldStage (restrictIndex κ s) (k + 1) ∨
    (G.pullback (Subtype.val : {v : V // v ∈ s} → V)).toPredimension.IsMinimalStrongStep
      (oldStage (restrictIndex κ s) k)
      (oldStage (restrictIndex κ s) (k + 1))
  intro k hk
  rcases hSteps k hk with hEq | hMin
  · left
    apply Finset.image_injective
      (Subtype.val_injective :
        Function.Injective (Subtype.val : {v : V // v ∈ s} → V))
    rw [oldStage_restrict_image κ s k,
      oldStage_restrict_image κ s (k + 1), hEq]
  · rcases canonicalValue_restrict_minimalStep_at
        G κ s hClosed k hk hMin with hEqual | hStep
    · exact Or.inl hEqual.symm
    · exact Or.inr hStep

/-- Restriction to a complete-unary-closed finite set retains both
the empty-or-minimal strong presentation and **all** complete unary
values, not just the graph reduct or a weaker closure inclusion. -/
theorem canonicalValue_restrict_fullPresentation
    (G : GraphOn V) (κ : V → Fin n)
    (hSteps : ∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k + 1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k + 1)))
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (canonicalValue G κ) s) :
    let H := G.pullback
      (Subtype.val : {v : V // v ∈ s} → V)
    let κs := restrictIndex κ s
    (∀ k : ℕ, k < n →
      oldStage κs k = oldStage κs (k + 1) ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage κs k) (oldStage κs (k + 1))) ∧
    (∀ u : {v : V // v ∈ s},
      (canonicalValue H κs u).image
        (Subtype.val : {v : V // v ∈ s} → V) =
      canonicalValue G κ u.val) := by
  exact ⟨canonicalValue_restrict_emptyOrMinimalSteps
    G κ hSteps s hClosed,
    canonicalValue_restrict_image G κ s hClosed⟩

end FiniteC0
end BigHrushovski
