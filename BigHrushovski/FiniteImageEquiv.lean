import BigHrushovski.SpanNormalization

/-!
# An equivalence between a finite carrier and its actual image

An injective map from a finite type A into a type B induces a
bijection from A to the subtype of B consisting of precisely those
vertices in the finite image of the map. Unlike an arbitrary choice
of finite enumeration, the forward equivalence has literal value
f(a) at every source vertex.

This is the final carrier normalization needed when a finite
strong induced extension is packaged as a finite partial
isomorphism with its actual finite image as target.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {A B : Type*}
variable [Fintype A] [DecidableEq A] [DecidableEq B]

/-- Canonical equivalence of the source with the actual finite image
of an injective map, not merely with an isomorphic finite set. -/
noncomputable def finiteImageEquiv
    (f : A → B) (hf : Function.Injective f) :
    A ≃ {b : B // b ∈ (Finset.univ : Finset A).image f} := by
  classical
  exact
    { toFun := fun a =>
        ⟨f a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
      invFun := fun b =>
        Classical.choose (Finset.mem_image.mp b.property)
      left_inv := by
        intro a
        apply hf
        exact (Classical.choose_spec
          (Finset.mem_image.mp
            (Finset.mem_image.mpr
              ⟨a, Finset.mem_univ _, rfl⟩))).2
      right_inv := by
        intro b
        apply Subtype.ext
        exact (Classical.choose_spec
          (Finset.mem_image.mp b.property)).2 }

/-- The canonical finite-image equivalence retains the precise
output vertex of the original embedding pointwise. -/
@[simp] theorem finiteImageEquiv_apply_val
    (f : A → B) (hf : Function.Injective f) (a : A) :
    (finiteImageEquiv f hf a).val = f a := rfl

/-- Every vertex in the finite image has the canonical preimage
given by the inverse of the finite-image equivalence. -/
@[simp] theorem finiteImageEquiv_symm_val
    (f : A → B) (hf : Function.Injective f)
    (b : {b : B // b ∈ (Finset.univ : Finset A).image f}) :
    f ((finiteImageEquiv f hf).symm b) = b.val := by
  have h := (finiteImageEquiv f hf).apply_symm_apply b
  exact congrArg Subtype.val h

end FiniteSpan
end BigHrushovski
