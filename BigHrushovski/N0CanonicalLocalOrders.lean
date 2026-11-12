import BigHrushovski.N0CanonicalLocalFibres
import BigHrushovski.N0EnumerationOrders
import Mathlib.Tactic

/-!
# Canonical local fibres as actual labelled linear orders

The finite local factor g_A(B) counts distinct orders on the induced
successor closure C_B, not just abstract enumeration records. A bijective
enumeration determines its order relation injectively; the canonical
complete-adjacency-code class therefore contains exactly g_A(B)
different strict orders.

The restriction of every such order to the lower successor part P_B
agrees literally with the prescribed lower-part order. Neither
identification quotients by the automorphism group.

This does not yet produce a bijection between global permitted orders
and tuples of such local orders. Compatibility between overlapping
closures and the surjectivity of global reconstruction remain open.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Equality of positions at all old vertices gives equality of their
inverse enumeration indices, not merely equality of the unordered
old vertex set. -/
theorem sameLowerPositions_inverse_eq
    (P : Finset V) {n : ℕ} (base f : Fin n ≃ V)
    (hOld : SameLowerPositions P base f)
    {x : V} (hx : x ∈ P) :
    base.symm x = f.symm x := by
  have hIn : base (base.symm x) ∈ P := by
    simpa using hx
  have hFix : f (base.symm x) = x := by
    simpa using hOld (base.symm x) hIn
  have hInv : f.symm x = base.symm x := by
    apply f.injective
    simpa [hFix]
  exact hInv.symm

/-- The induced order on the lower part is literally preserved
when the two full enumerations agree at all old positions. -/
theorem sameLowerPositions_preserves_old_order
    (P : Finset V) {n : ℕ} (base f : Fin n ≃ V)
    (hOld : SameLowerPositions P base f)
    {u v : V} (hu : u ∈ P) (hv : v ∈ P) :
    (OrderBefore base u v ↔ OrderBefore f u v) := by
  unfold OrderBefore
  rw [sameLowerPositions_inverse_eq P base f hOld hu,
    sameLowerPositions_inverse_eq P base f hOld hv]

variable (O : FiniteOrientation V)

/-- The actual labelled strict linear orders corresponding to the
canonical local class on the induced closure C_B. -/
noncomputable def canonicalComponentOrderRelations
    (x : V) {n : ℕ} (base : Fin n ≃ O.componentClosure x) :
    Finset (O.componentClosure x →
      O.componentClosure x → Prop) := by
  classical
  exact (O.canonicalComponentLexClass x base).image OrderBefore

/-- The canonical local factor counts *distinct labelled orders*
on C_B, rather than formal descriptions of the same order. -/
theorem canonicalComponentOrderRelations_card
    (x : V) {n : ℕ} (base : Fin n ≃ O.componentClosure x) :
    (O.canonicalComponentOrderRelations x base).card =
      O.actualLocalFactor x := by
  classical
  calc
    (O.canonicalComponentOrderRelations x base).card =
        (O.canonicalComponentLexClass x base).card := by
      unfold canonicalComponentOrderRelations
      apply Finset.card_image_iff.mpr
      intro f _ g _ h
      exact orderBefore_injective h
    _ = O.actualLocalFactor x :=
      O.canonicalComponentLexClass_card x base

/-- Every canonical labelled order extends the exact order of the
prescribed old part, including every comparison of nonadjacent old
vertices. -/
theorem canonicalComponentOrderRelations_agree_on_lower
    (x : V) {n : ℕ}
    (base : Fin n ≃ O.componentClosure x)
    {R : O.componentClosure x → O.componentClosure x → Prop}
    (hR : R ∈ O.canonicalComponentOrderRelations x base)
    {u v : O.componentClosure x}
    (hu : u ∈ O.inducedLowerPart x)
    (hv : v ∈ O.inducedLowerPart x) :
    (R u v ↔ OrderBefore base u v) := by
  classical
  change R ∈ (O.canonicalComponentLexClass x base).image
    OrderBefore at hR
  obtain ⟨f, hf, hEq⟩ := Finset.mem_image.mp hR
  subst R
  have hOld : SameLowerPositions (O.inducedLowerPart x) base f :=
    O.canonicalComponentLexClass_fixedLower x base f hf
  exact (sameLowerPositions_preserves_old_order
    (O.inducedLowerPart x) base f hOld hu hv).symm

/-- The set of canonical labelled orders depends only on the
fixed ordering of the old positions, not on the initial enumeration
of the new component. -/
theorem canonicalComponentOrderRelations_eq_of_sameLowerPositions
    (x : V) {n : ℕ}
    (base₁ base₂ : Fin n ≃ O.componentClosure x)
    (hbase : SameLowerPositions (O.inducedLowerPart x) base₁ base₂) :
    O.canonicalComponentOrderRelations x base₁ =
      O.canonicalComponentOrderRelations x base₂ := by
  unfold canonicalComponentOrderRelations
  rw [O.canonicalComponentLexClass_eq_of_sameLowerPositions
    x base₁ base₂ hbase]

/-- Component-indexed canonical *order* count for the true
induced orientation on C_B. -/
theorem componentCanonicalOrderRelations_card
    (B : O.ComponentObject) {n : ℕ}
    (base : Fin n ≃ O.componentClosure (O.componentGenerator B)) :
    (O.canonicalComponentOrderRelations
      (O.componentGenerator B) base).card =
    O.componentLocalFactor B := by
  exact O.canonicalComponentOrderRelations_card
    (O.componentGenerator B) base

end FiniteOrientation
end BigHrushovski
