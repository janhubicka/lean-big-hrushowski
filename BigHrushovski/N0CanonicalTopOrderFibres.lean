import BigHrushovski.N0CanonicalLocalOrders
import Mathlib.Tactic

/-!
# Canonical local fibres as genuine choices of the top component order

For an actual strongly connected component B of a finite orientation,
write C_B for its complete successor closure and P_B for its strict
lower part. An admissible component-closure enumeration lists P_B
before B. Once its lower-part positions are fixed, restriction to
the order on B is injective: the old order and the new order together
determine the whole order on C_B.

Therefore the canonical complete-code fibre contributes exactly
g_A(B) *distinct labelled orders on the top component B*, not
merely g_A(B) enumerations of the larger closure.

The result is finite. It does not yet prove that the recursive global
assembly has uniform fibres or the finite degree product formula.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The old part is an initial segment of a finite enumeration:
every old vertex precedes every new vertex. -/
def IsLowerBeforeRest (P : Finset V) {n : ℕ}
    (e : Fin n ≃ V) : Prop :=
  ∀ u v : V, u ∈ P → v ∉ P → OrderBefore e u v

/-- Fixing all old positions preserves the initial-segment condition.
The remaining positions cannot receive old vertices, by injectivity. -/
theorem lowerBeforeRest_of_sameLowerPositions
    (P : Finset V) {n : ℕ}
    (base e : Fin n ≃ V)
    (hInitial : IsLowerBeforeRest P base)
    (hOld : SameLowerPositions P base e) :
    IsLowerBeforeRest P e := by
  intro u v hu hv
  have huPosition : base.symm u = e.symm u :=
    sameLowerPositions_inverse_eq P base e hOld hu
  have hvNew : base (e.symm v) ∉ P := by
    intro hBaseOld
    have hFix := hOld (e.symm v) hBaseOld
    have hvEq : v = base (e.symm v) := by
      simpa using hFix
    exact hv (hvEq.symm ▸ hBaseOld)
  have hBefore := hInitial u (base (e.symm v)) hu hvNew
  change base.symm u < base.symm (base (e.symm v)) at hBefore
  change e.symm u < e.symm v
  simpa only [Equiv.symm_apply_apply, huPosition] using hBefore

/-- The complement of the fixed old part, as an actual labelled type. -/
abbrev RemainingVertices (P : Finset V) := {u : V // u ∉ P}

/-- All strict comparisons on the remaining vertices in a complete
enumeration. No quotient by graph automorphisms is taken. -/
def RemainingOrder (P : Finset V) {n : ℕ}
    (e : Fin n ≃ V) :
    RemainingVertices P → RemainingVertices P → Prop :=
  fun u v => OrderBefore e u.val v.val

/-- If two complete enumerations fix the same old positions,
put the old part first, and agree on all comparisons within
the new part, then they are literally the same enumeration.

The initial-segment hypothesis is essential: without it, the
old vertices can be interleaved with the new ones differently. -/
theorem enumeration_eq_of_fixed_old_and_same_remaining_order
    (P : Finset V) {n : ℕ}
    (base e f : Fin n ≃ V)
    (heOld : SameLowerPositions P base e)
    (hfOld : SameLowerPositions P base f)
    (heInitial : IsLowerBeforeRest P e)
    (hfInitial : IsLowerBeforeRest P f)
    (hRemaining : RemainingOrder P e = RemainingOrder P f) :
    e = f := by
  apply enumeration_eq_of_same_order e f
  intro x y
  by_cases hx : x ∈ P
  · by_cases hy : y ∈ P
    · have hxE := sameLowerPositions_inverse_eq P base e heOld hx
      have hyE := sameLowerPositions_inverse_eq P base e heOld hy
      have hxF := sameLowerPositions_inverse_eq P base f hfOld hx
      have hyF := sameLowerPositions_inverse_eq P base f hfOld hy
      change e.symm x < e.symm y ↔ f.symm x < f.symm y
      rw [← hxE, ← hyE, ← hxF, ← hyF]
    · exact ⟨fun _ => hfInitial x y hx hy,
        fun _ => heInitial x y hx hy⟩
  · by_cases hy : y ∈ P
    · have heNot : ¬ OrderBefore e x y := by
        intro h
        exact lt_asymm (heInitial y x hy hx) h
      have hfNot : ¬ OrderBefore f x y := by
        intro h
        exact lt_asymm (hfInitial y x hy hx) h
      exact ⟨fun h => (heNot h).elim,
        fun h => (hfNot h).elim⟩
    · have h : RemainingOrder P e
          ⟨x, hx⟩ ⟨y, hy⟩ =
          RemainingOrder P f ⟨x, hx⟩ ⟨y, hy⟩ :=
        congrFun (congrFun hRemaining ⟨x, hx⟩) ⟨y, hy⟩
      change OrderBefore e x y = OrderBefore f x y at h
      exact ⟨fun p => h ▸ p, fun p => h.symm ▸ p⟩

variable (O : FiniteOrientation V)

/-- For an induced one-component closure, the complement of
the lower part really is the top SCC, as a labelled set. -/
theorem not_mem_inducedLowerPart_iff_mem_component
    (x : V) (u : O.componentClosure x) :
    u ∉ O.inducedLowerPart x ↔ u.val ∈ O.component x := by
  change ¬ u.val ∈ O.lowerPart x ↔ u.val ∈ O.component x
  simp only [lowerPart, Finset.mem_sdiff, u.property, true_and, not_not]

/-- Each canonical local enumeration determines a strict order
on the complement of the old part, hence on the top component. -/
noncomputable def canonicalTopOrderRelations
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x) :
    Finset (RemainingVertices (O.inducedLowerPart x) →
      RemainingVertices (O.inducedLowerPart x) → Prop) := by
  classical
  exact (O.canonicalComponentLexClass x base).image
    (RemainingOrder (O.inducedLowerPart x))

/-- With P_B first in the prescribed base, the canonical fibre
gives exactly g_A(B) *distinct top-component orders*.

The original local fibre count alone did not identify different
complete enumerations with different new-component orders; the
injectivity proof here supplies that missing assertion. -/
theorem canonicalTopOrderRelations_card
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x)
    (hInitial : IsLowerBeforeRest (O.inducedLowerPart x) base) :
    (O.canonicalTopOrderRelations x base).card =
      O.actualLocalFactor x := by
  classical
  calc
    (O.canonicalTopOrderRelations x base).card =
        (O.canonicalComponentLexClass x base).card := by
      unfold canonicalTopOrderRelations
      apply Finset.card_image_iff.mpr
      intro e he f hf hRemaining
      have heOld := O.canonicalComponentLexClass_fixedLower
        x base e he
      have hfOld := O.canonicalComponentLexClass_fixedLower
        x base f hf
      apply enumeration_eq_of_fixed_old_and_same_remaining_order
        (O.inducedLowerPart x) base e f heOld hfOld
      · exact lowerBeforeRest_of_sameLowerPositions
          (O.inducedLowerPart x) base e hInitial heOld
      · exact lowerBeforeRest_of_sameLowerPositions
          (O.inducedLowerPart x) base f hInitial hfOld
      · exact hRemaining
    _ = O.actualLocalFactor x :=
      O.canonicalComponentLexClass_card x base

/-- Component-indexed formulation of the true local factor. -/
theorem componentCanonicalTopOrderRelations_card
    (B : O.ComponentObject) {n : ℕ}
    (base : Fin n ≃
      O.componentClosure (O.componentGenerator B))
    (hInitial : IsLowerBeforeRest
      (O.inducedLowerPart (O.componentGenerator B)) base) :
    (O.canonicalTopOrderRelations (O.componentGenerator B) base).card =
      O.componentLocalFactor B :=
  O.canonicalTopOrderRelations_card
    (O.componentGenerator B) base hInitial

end FiniteOrientation
end BigHrushovski
