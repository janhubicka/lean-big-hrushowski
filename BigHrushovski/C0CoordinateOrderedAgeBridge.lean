import BigHrushovski.C0CoordinateInducedCode
import BigHrushovski.C0CoordinatePointedAgeCode

/-!
# A finite C₀ code-to-age bridge

The finite coordinate-host construction requires two distinct facts:

1. A complete pointed code restricted to a finite C-closed domain is
   exactly the code of the induced finite functional substructure.
2. This induced structure has the inherited minimal-strong component
   presentation. Its order must also respect the chronology of these
   components.

The code equality is independent of closedness. The functional-age
assertions explicitly require closedness and minimal-strong steps.
Chronological component order is likewise an explicit assumption:
it does NOT assert the stronger manuscript convention selecting one
ordered representative for each one-generated closure type.

No countable host W, return map, or Ramsey theorem is asserted here.
-/

namespace BigHrushovski

namespace FiniteUnaryCoordinates

variable {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
variable {n : ℕ}

/-- Different component indices are ordered according to their
chronological order. This is a necessary, but not sufficient, clause
of the manuscript's closure-respecting order convention. -/
def ChronologicalBlockOrder (κ : V → Fin n) : Prop :=
  ∀ u v : V, κ u < κ v → u < v

/-- Chronological order makes each complete component an interval
of the finite linear order. -/
theorem chronologicalBlockOrder_interval
    (κ : V → Fin n) (h : ChronologicalBlockOrder κ)
    (x y z : V) (hxy : κ x = κ y)
    (hxz : x < z) (hzy : z < y) :
    κ z = κ x := by
  rcases lt_trichotomy (κ z) (κ x) with hlt | heq | hgt
  · exact False.elim (lt_asymm (h z x hlt) hxz)
  · exact heq
  · have hyz : y < z := h y z (by simpa [hxy] using hgt)
    exact False.elim (lt_asymm hyz hzy)

/-- Taking an induced finite subtype does not disrupt the
chronological order of its retained complete components. -/
theorem chronologicalBlockOrder_restrict
    (κ : V → Fin n) (s : Finset V)
    (h : ChronologicalBlockOrder κ) :
    ChronologicalBlockOrder (FiniteC0.restrictIndex κ s) := by
  intro u v huv
  exact h u.val v.val huv

/-- An arbitrary finite canonical C₀ presentation and a C-closed
subdomain yield the same literal code as the induced graph/function,
and the induced domain has an empty-or-minimal-strong component
presentation. The original pointed root may lie OUTSIDE the
selected domain; u is the new distinguished point.

The order hypothesis is separate and means only that different
components occur in chronological order. The fixed internal ordered
representatives of the manuscript still require another condition. -/
theorem canonicalClosed_code_age_bridge
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k) (FiniteC0.oldStage κ (k + 1)))
    (hOrder : ChronologicalBlockOrder κ)
    (e : V ↪o ℕ)
    (s : Finset V)
    (hClosed : G.IsClosedUnderValues (FiniteC0.canonicalValue G κ) s)
    (root : V) (u : s) :
    (literalPointedCode G (FiniteC0.canonicalValue G κ) e root).restrictTo
       (s.image e) (coordinateImage_subset_labelSupport e s)
       (e u.val) ((mem_coordinateImage_iff e s u.val).mpr u.property) =
      literalPointedCode (restrictGraph G s)
        (restrictValue (FiniteC0.canonicalValue G κ) s)
        (restrictedLabel e s) u
    ∧ ChronologicalBlockOrder (FiniteC0.restrictIndex κ s)
    ∧ (∀ v : s,
       (FiniteC0.canonicalValue
         (G.pullback (Subtype.val : s → V))
         (FiniteC0.restrictIndex κ s) v).image
           (Subtype.val : s → V) =
         FiniteC0.canonicalValue G κ v.val)
    ∧ (∀ k : ℕ, k < n →
       let H := G.pullback (Subtype.val : s → V)
       let κs := FiniteC0.restrictIndex κ s
       FiniteC0.oldStage κs (k + 1) = FiniteC0.oldStage κs k ∨
         H.toPredimension.IsMinimalStrongStep
           (FiniteC0.oldStage κs k) (FiniteC0.oldStage κs (k + 1))) := by
  classical
  refine ⟨literalPointedCode_restrict_eq
      G (FiniteC0.canonicalValue G κ) e root s u,
    chronologicalBlockOrder_restrict κ s hOrder, ?_, ?_⟩
  · intro v
    exact FiniteC0.canonicalValue_restrict_image
      G κ s hClosed v
  · intro k hk
    exact FiniteC0.canonicalValue_restrict_minimalSteps
      G κ hMin s hClosed k hk

/-- A one-generated canonical C₀ closure satisfies the preceding
finite-age and code conditions, including the complete named
functions and the chronological component order. Reflexivity and
the minimal-step certificate are not hidden hypotheses. -/
theorem canonicalOneGenerated_code_age_bridge
    (G : GraphOn V) (κ : V → Fin n)
    (hMin : ∀ k : ℕ, k < n →
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ k) (FiniteC0.oldStage κ (k + 1)))
    (hOrder : ChronologicalBlockOrder κ)
    (e : V ↪o ℕ) (a : V) :
    let s := FiniteC0.canonicalValue G κ a
    let u : s := ⟨a, FiniteC0.canonicalValue_mem_self G κ a⟩
    (literalPointedCode G (FiniteC0.canonicalValue G κ) e a).restrictTo
       (s.image e) (coordinateImage_subset_labelSupport e s)
       (e u.val) ((mem_coordinateImage_iff e s u.val).mpr u.property) =
      literalPointedCode (restrictGraph G s)
        (restrictValue (FiniteC0.canonicalValue G κ) s)
        (restrictedLabel e s) u
    ∧ ChronologicalBlockOrder (FiniteC0.restrictIndex κ s)
    ∧ (∀ v : s,
       (FiniteC0.canonicalValue
         (G.pullback (Subtype.val : s → V))
         (FiniteC0.restrictIndex κ s) v).image
           (Subtype.val : s → V) =
         FiniteC0.canonicalValue G κ v.val)
    ∧ (∀ k : ℕ, k < n →
       let H := G.pullback (Subtype.val : s → V)
       let κs := FiniteC0.restrictIndex κ s
       FiniteC0.oldStage κs (k + 1) = FiniteC0.oldStage κs k ∨
         H.toPredimension.IsMinimalStrongStep
           (FiniteC0.oldStage κs k) (FiniteC0.oldStage κs (k + 1))) := by
  exact canonicalClosed_code_age_bridge G κ hMin hOrder e
    (FiniteC0.canonicalValue G κ a)
    (FiniteC0.canonicalValue_oneGenerated_closed G κ a)
    a ⟨a, FiniteC0.canonicalValue_mem_self G κ a⟩

end FiniteUnaryCoordinates
end BigHrushovski
