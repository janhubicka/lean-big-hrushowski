import BigHrushovski.SpanNormalization

/-!
# Complete finite unary values from two covering factor images

Suppose a finite amalgam has two factor embeddings whose images
cover its carrier. The complete named unary values on the amalgam
are known on both factor images. Suppose further that an equivalence
to the intended literal union carries the complete unary values
correctly on each factor. Then it carries them correctly EVERYWHERE.

This elementary finite transfer is reusable for C₀ and C_F.
It has no graph, predimension or component-order hypotheses. Graph
reflection, the two-sided finite amalgamation theorem, and the
literal-union carrier equivalence are separate inputs.
-/

namespace BigHrushovski
namespace FiniteFunctionalTransfer

variable {A B X Y : Type*}
variable [DecidableEq A] [DecidableEq B]
variable [DecidableEq X] [DecidableEq Y]

/-- Complete unary-value transport from a two-factor covering of
the amalgam carrier. Every image is an EQUALITY, not an inclusion;
thus every negative unary incidence is also reflected. -/
theorem completeValues_transport_of_two_factor_cover
    (f : A → X) (g : B → X) (e : X ≃ Y)
    (CA : A → Finset A) (CB : B → Finset B)
    (CX : X → Finset X) (CY : Y → Finset Y)
    (hCover : ∀ x : X, (∃ a : A, f a = x) ∨ (∃ b : B, g b = x))
    (hXLeft : ∀ a : A, CX (f a) = (CA a).image f)
    (hXRight : ∀ b : B, CX (g b) = (CB b).image g)
    (hYLeft : ∀ a : A, (CA a).image (e ∘ f) = CY (e (f a)))
    (hYRight : ∀ b : B, (CB b).image (e ∘ g) = CY (e (g b))) :
    ∀ x : X, (CX x).image e = CY (e x) := by
  classical
  intro x
  rcases hCover x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · calc
      (CX (f a)).image e =
          ((CA a).image f).image e := by rw [hXLeft a]
      _ = (CA a).image (e ∘ f) := Finset.image_image
      _ = CY (e (f a)) := hYLeft a
  · calc
      (CX (g b)).image e =
          ((CB b).image g).image e := by rw [hXRight b]
      _ = (CB b).image (e ∘ g) := Finset.image_image
      _ = CY (e (g b)) := hYRight b

/-- The standard tagged common-base/two-tail carrier is covered
by the two exact factor embeddings. This requires no property of
either factor's graph or unary values, and includes empty tails. -/
theorem taggedCarrier_twoFactor_cover
    {P L R : Type*} :
    ∀ x : TaggedAmalgam.Carrier P L R,
      (∃ u : P ⊕ L, TaggedAmalgam.leftTag u = x) ∨
      (∃ v : P ⊕ R, TaggedAmalgam.rightTag v = x) := by
  intro x
  cases x with
  | inl p =>
      exact Or.inl ⟨Sum.inl p, rfl⟩
  | inr t =>
      cases t with
      | inl l =>
          exact Or.inl ⟨Sum.inr l, rfl⟩
      | inr r =>
          exact Or.inr ⟨Sum.inr r, rfl⟩

/-- The actual normalized finite two-sided amalgam, with arbitrary
embeddings of a common base, is covered by the two original factor
images. In particular no extra anonymous amalgam vertices exist. -/
theorem normalizedAmalgam_twoFactor_cover
    {P A B : Type*}
    (i : P → A) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∀ x : TaggedAmalgam.Carrier P
        (FiniteSpan.Tail i) (FiniteSpan.Tail j),
      (∃ a : A, FiniteSpan.leftAmalgamEmbedding i hi j a = x) ∨
      (∃ b : B, FiniteSpan.rightAmalgamEmbedding i j hj b = x) := by
  intro x
  rcases taggedCarrier_twoFactor_cover x with ⟨u, hu⟩ | ⟨v, hv⟩
  · left
    refine ⟨FiniteSpan.splitEquiv i hi u, ?_⟩
    change TaggedAmalgam.leftTag
      ((FiniteSpan.splitEquiv i hi).symm (FiniteSpan.splitEquiv i hi u)) = x
    rw [Equiv.symm_apply_apply]
    exact hu
  · right
    refine ⟨FiniteSpan.splitEquiv j hj v, ?_⟩
    change TaggedAmalgam.rightTag
      ((FiniteSpan.splitEquiv j hj).symm (FiniteSpan.splitEquiv j hj v)) = x
    rw [Equiv.symm_apply_apply]
    exact hv

end FiniteFunctionalTransfer
end BigHrushovski
