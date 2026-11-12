import BigHrushovski.N0CanonicalLocalFibres
import Mathlib.Tactic

/-!
# An elementary criterion for canonical finite component orders

Membership in the least complete adjacency-code class is equivalent
to two direct requirements: the new enumeration fixes every position
of the already ordered lower part, and no enumeration fixing these
positions has a smaller complete row-major directed adjacency code.

This gives a convenient mathematical formulation of the finite
ordered-representative convention. The proof does not count global
orders and makes no infinite Ramsey claim.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A member of a nonempty finite family has minimum code precisely
when its code is no greater than that of every member. The criterion
retains the membership requirement: being small outside the family
does not suffice. -/
theorem mem_minimumCodeClass_iff_le_all
    {n : ℕ} {κ : Type*} [LinearOrder κ]
    (choices : Finset (Fin n ≃ V))
    (code : (Fin n ≃ V) → κ)
    (hne : choices.Nonempty)
    (e : Fin n ≃ V) :
    e ∈ minimumCodeClass choices code hne ↔
      e ∈ choices ∧ ∀ f ∈ choices, code e ≤ code f := by
  classical
  constructor
  · intro he
    exact ⟨((mem_minimumCodeClass_iff choices code hne e).mp he).1,
      fun f hf => minimumCodeClass_is_minimal choices code hne he hf⟩
  · rintro ⟨he, hLeast⟩
    apply (mem_minimumCodeClass_iff choices code hne e).mpr
    refine ⟨he, ?_⟩
    let m : κ := (choices.image code).min'
      (Finset.image_nonempty.mpr hne)
    have hm : m ∈ choices.image code :=
      Finset.min'_mem _ _
    obtain ⟨f, hf, hfm⟩ := Finset.mem_image.mp hm
    have hem : code e ≤ m := by
      calc
        code e ≤ code f := hLeast f hf
        _ = m := hfm
    have hme : m ≤ code e :=
      Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    exact le_antisymm hem hme

variable (O : FiniteOrientation V)

/-- A local complete enumeration is canonical exactly when its
row-major directed adjacency code is least among all complete
enumerations that keep the lower successor part fixed pointwise
at the same old positions. This retains both edges and nonedges. -/
theorem mem_canonicalComponentLexClass_iff_le_all
    (x : V) {n : ℕ}
    (base e : Fin n ≃ O.componentClosure x) :
    e ∈ O.canonicalComponentLexClass x base ↔
      SameLowerPositions (O.inducedLowerPart x) base e ∧
      ∀ f : Fin n ≃ O.componentClosure x,
        SameLowerPositions (O.inducedLowerPart x) base f →
        (O.inducedComponentOrientation x).completeRowMajorLexCode e ≤
          (O.inducedComponentOrientation x).completeRowMajorLexCode f := by
  classical
  simpa only [canonicalComponentLexClass,
    mem_minimumCodeClass_iff_le_all, mem_fixedLowerEnumerations_iff]

/-- The criterion is invariant under the arbitrary order initially
assigned to the new component, provided the old positions agree.
This uses the previously certified equality of entire canonical
classes, not merely equality of their cardinalities. -/
theorem canonicalComponentLexCriterion_base_independent
    (x : V) {n : ℕ}
    (base₁ base₂ e : Fin n ≃ O.componentClosure x)
    (hbase : SameLowerPositions (O.inducedLowerPart x) base₁ base₂) :
    (SameLowerPositions (O.inducedLowerPart x) base₁ e ∧
      ∀ f : Fin n ≃ O.componentClosure x,
        SameLowerPositions (O.inducedLowerPart x) base₁ f →
        (O.inducedComponentOrientation x).completeRowMajorLexCode e ≤
          (O.inducedComponentOrientation x).completeRowMajorLexCode f) ↔
    (SameLowerPositions (O.inducedLowerPart x) base₂ e ∧
      ∀ f : Fin n ≃ O.componentClosure x,
        SameLowerPositions (O.inducedLowerPart x) base₂ f →
        (O.inducedComponentOrientation x).completeRowMajorLexCode e ≤
          (O.inducedComponentOrientation x).completeRowMajorLexCode f) := by
  calc
    _ ↔ e ∈ O.canonicalComponentLexClass x base₁ :=
      (O.mem_canonicalComponentLexClass_iff_le_all x base₁ e).symm
    _ ↔ e ∈ O.canonicalComponentLexClass x base₂ := by
      rw [O.canonicalComponentLexClass_eq_of_sameLowerPositions
        x base₁ base₂ hbase]
    _ ↔ _ := O.mem_canonicalComponentLexClass_iff_le_all x base₂ e

end FiniteOrientation
end BigHrushovski
