import BigHrushovski.C0ClosedBaseFrontload
import BigHrushovski.C0FiniteCanonicalRestriction

/-!
# Finite C0 functional age and its hereditary property

The finite C0 age is described without choosing a canonical witness
order in the language. A finite graph G with set-valued unary
function F belongs to the class if there exists a component indexing
κ:V→Fin n such that every successive stage is either unchanged
(an unused component position) or minimal strong, and F agrees
exactly with the full canonical backward component closure.

For a finite F-closed vertex set S we restrict the graph and the
*named unary function* to the induced subtype S. By frontloading
S in the witnessing presentation, its old stages inherit
empty-or-minimal strong steps. The complete inherited values
are unchanged by the canonical closed-restriction theorem.

This is the full finite hereditary property of the functional
age, including its function values, not merely graph strongness.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Intrinsic membership of a finite graph with a named complete
set-valued C0 unary function in the finite functional age.
The chronological component indexing is an existential witness,
not part of the language. Empty component slots are harmless. -/
def HasFiniteFunctionalPresentation
    (G : GraphOn V) (F : V → Finset V) : Prop :=
  ∃ (n : ℕ) (κ : V → Fin n),
    (∀ k : ℕ, k < n →
      oldStage κ k = oldStage κ (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (oldStage κ k) (oldStage κ (k+1))) ∧
    (∀ v : V, F v = canonicalValue G κ v)

/-- The induced set-valued unary function on the closed finite
subtype, with values represented directly as subsets of that subtype. -/
noncomputable def restrictedValues
    (F : V → Finset V) (s : Finset V)
    (u : {v : V // v ∈ s}) : Finset {v : V // v ∈ s} := by
  classical
  exact Finset.univ.filter (fun v => v.val ∈ F u.val)

/-- Every finite subset closed under F inherits a canonical
functional C0 presentation, with the exact restricted values,
independently of the witness component order on the ambient
structure. -/
theorem hasFiniteFunctionalPresentation_closed_restrict
    (G : GraphOn V) (F : V → Finset V)
    (hPresent : HasFiniteFunctionalPresentation G F)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues F s) :
    HasFiniteFunctionalPresentation
      (G.pullback (Subtype.val : {v : V // v ∈ s} → V))
      (restrictedValues F s) := by
  classical
  obtain ⟨n, κ, hMin, hValues⟩ := hPresent
  let H : GraphOn {v : V // v ∈ s} :=
    G.pullback (Subtype.val : {v : V // v ∈ s} → V)
  let κs := restrictIndex κ s
  have hClosedκ : G.IsClosedUnderValues
      (canonicalValue G κ) s := by
    intro v hv
    rw [← hValues v]
    exact hClosed v hv
  have hFront :=
    frontloadIndex_minimal_steps G κ s hClosedκ hMin
  have hSteps : ∀ k : ℕ, k < n →
      oldStage κs k = oldStage κs (k+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (oldStage κs k) (oldStage κs (k+1)) := by
    intro k hk
    rcases hFront k (by omega) with hEqual | hMinimal
    · left
      have hCut : s ∩ oldStage κ k =
          s ∩ oldStage κ (k+1) := by
        rw [oldStage_frontload_first κ s k (by omega),
          oldStage_frontload_first κ s (k+1) (by omega)] at hEqual
        exact hEqual
      apply Finset.image_injective
        (Subtype.val_injective : Function.Injective
          (Subtype.val : {v : V // v ∈ s} → V))
      rw [oldStage_restrict_image κ s k,
          oldStage_restrict_image κ s (k+1)]
      exact hCut
    · right
      have hSubset : oldStage κs k ⊆ oldStage κs (k+1) := by
        intro u hu
        have hLess := (mem_oldStage_iff κs k u).mp hu
        exact (mem_oldStage_iff κs (k+1) u).mpr (by omega)
      have hCut : G.toPredimension.IsMinimalStrongStep
          (s ∩ oldStage κ k) (s ∩ oldStage κ (k+1)) := by
        rw [oldStage_frontload_first κ s k (by omega),
          oldStage_frontload_first κ s (k+1) (by omega)] at hMinimal
        exact hMinimal
      have hImage : G.toPredimension.IsMinimalStrongStep
          ((oldStage κs k).image
            (Subtype.val : {v : V // v ∈ s} → V))
          ((oldStage κs (k+1)).image
            (Subtype.val : {v : V // v ∈ s} → V)) := by
        rw [oldStage_restrict_image κ s k,
          oldStage_restrict_image κ s (k+1)]
        exact hCut
      have hAdj : ∀ u v : {v : V // v ∈ s},
          H.adj u v ↔ G.adj u.val v.val := fun _ _ => Iff.rfl
      exact (H.minimalStrongStep_image_iff G
        (Subtype.val : {v : V // v ∈ s} → V)
        Subtype.val_injective hAdj
        (oldStage κs k) (oldStage κs (k+1)) hSubset).mp hImage
  have hFunction : ∀ u : {v : V // v ∈ s},
      restrictedValues F s u = canonicalValue H κs u := by
    intro u
    ext w
    simp only [restrictedValues, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hValues u.val]
    have hAnc := restrictAncestor_iff G κ s hClosedκ u (κ w.val)
    exact (mem_canonicalValue_iff G κ u.val w.val).trans
      (hAnc.symm.trans
        (mem_canonicalValue_iff H κs u w).symm)
  exact ⟨n, κs, hSteps, hFunction⟩

end FiniteC0
end BigHrushovski
