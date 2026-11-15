import BigHrushovski.FiniteSetTaggedUnion
import BigHrushovski.C0CoordinateRawClosedOverlap
import BigHrushovski.SpanNormalization

/-!
# The normalized finite amalgam carrier is the literal raw-host union

The two-sided finite functional amalgamation theorem uses the
normalized carrier

  Carrier P (Tail i) (Tail j),

where P is the common finite base and i:P→S, j:P→T are injective.

For literal finite raw-host subsets S,T with P=S∩T, the two
abstract tails of these inclusions are just the exclusive parts
S\\T and T\\S. We identify them by explicit equivalences and
compose with the reusable tagged finite-union equivalence.

This supplies the exact finite carrier transport needed to compare
the amalgam's complete graph and unary functions with the raw-host
structure induced on S∪T. It does not yet prove those graph/function
comparisons or the converse finite-age theorem itself.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable [DecidableEq RawC0CoordinateVertex]

/-- The tail of the literal base inclusion P→S is exactly S\\T.
A raw-host vertex is never identified with another merely because
their pointed coordinates agree. -/
noncomputable def RawC0CoordinateVertex.overlapLeftTailEquiv
    (s t : Finset RawC0CoordinateVertex) :
    FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t) ≃
      FiniteSetUnion.LeftOnly s t where
  toFun x := by
    classical
    refine ⟨x.val.val, x.val.property, ?_⟩
    intro hxt
    apply x.property
    refine ⟨⟨x.val.val,Finset.mem_inter.mpr
      ⟨x.val.property,hxt⟩⟩, ?_⟩
    exact Subtype.ext rfl
  invFun y := by
    classical
    refine ⟨⟨y.val,y.property.1⟩, ?_⟩
    rintro ⟨p,hp⟩
    have hVal : p.val = y.val := congrArg Subtype.val hp
    have hPt : p.val ∈ t := (Finset.mem_inter.mp p.property).2
    exact y.property.2 (hVal ▸ hPt)
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

/-- The right normalized tail likewise consists exactly of T\\S. -/
noncomputable def RawC0CoordinateVertex.overlapRightTailEquiv
    (s t : Finset RawC0CoordinateVertex) :
    FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t) ≃
      FiniteSetUnion.RightOnly s t where
  toFun x := by
    classical
    refine ⟨x.val.val, x.val.property, ?_⟩
    intro hxs
    apply x.property
    refine ⟨⟨x.val.val,Finset.mem_inter.mpr
      ⟨hxs,x.val.property⟩⟩, ?_⟩
    exact Subtype.ext rfl
  invFun y := by
    classical
    refine ⟨⟨y.val,y.property.1⟩, ?_⟩
    rintro ⟨p,hp⟩
    have hVal : p.val = y.val := congrArg Subtype.val hp
    have hPs : p.val ∈ s := (Finset.mem_inter.mp p.property).1
    exact y.property.2 (hVal ▸ hPs)
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

/-- Equivalence of the abstract normalized three-tag carrier and
the literal common-base / two-exclusive-tails carrier. -/
noncomputable def RawC0CoordinateVertex.overlapNormalizedTaggedEquiv
    (s t : Finset RawC0CoordinateVertex) :
    TaggedAmalgam.Carrier
      {q : RawC0CoordinateVertex // q ∈ s ∩ t}
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t))
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t)) ≃
    FiniteSetUnion.TaggedCarrier s t :=
  Equiv.sumCongr (Equiv.refl _)
    (Equiv.sumCongr
      (RawC0CoordinateVertex.overlapLeftTailEquiv s t)
      (RawC0CoordinateVertex.overlapRightTailEquiv s t))

/-- The exact finite carrier of the verified two-sided functional
amalgam of literal raw-host subsets is equivalent to their actual
finite union. This is a bijection of vertices only: graph and
complete-unary compatibility must still be proved separately. -/
noncomputable def RawC0CoordinateVertex.normalizedAmalgamUnionEquiv
    (s t : Finset RawC0CoordinateVertex) :
    TaggedAmalgam.Carrier
      {q : RawC0CoordinateVertex // q ∈ s ∩ t}
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t))
      (FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t)) ≃
    {q : RawC0CoordinateVertex // q ∈ s ∪ t} :=
  (RawC0CoordinateVertex.overlapNormalizedTaggedEquiv s t).trans
    (FiniteSetUnion.taggedUnionEquiv s t)

end FiniteUnaryCoordinates
end BigHrushovski
