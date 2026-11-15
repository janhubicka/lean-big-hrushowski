import BigHrushovski.C0CoordinateNormalizedAmalgamUnion
import BigHrushovski.C0CoordinateRawClosedOverlap
import BigHrushovski.SpanNormalization

/-!
# Complete C-values on the factor images of a normalized finite amalgam

Let S,T be literal finite subsets of the preliminary raw C₀ host.
Write P=S∩T and form the normalized tagged amalgam carrier of the
two factor embeddings P→S and P→T.

The existing tagged carrier equivalence maps each original factor
vertex to its SAME raw vertex in the literal union. For C-closed
factors, it also transports every complete induced C-value exactly
onto its value in S∪T. These are the missing pointwise hypotheses
for the generic two-factor complete-value transport lemma.

The resulting statements do not yet produce a finite canonical
component index on S∪T; the functional amalgam and graph transport
are still separate proof steps.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable [DecidableEq RawC0CoordinateVertex]

/-- The literal common-base injection into the left finite factor
is injective on COMPLETE raw host vertices, not on coordinate labels. -/
theorem RawC0CoordinateVertex.overlapLeft_injective
    (s t : Finset RawC0CoordinateVertex) :
    Function.Injective (RawC0CoordinateVertex.overlapLeft s t) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : s => z.val) h

/-- The symmetric complete raw-vertex injection into the right factor. -/
theorem RawC0CoordinateVertex.overlapRight_injective
    (s t : Finset RawC0CoordinateVertex) :
    Function.Injective (RawC0CoordinateVertex.overlapRight s t) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : t => z.val) h

/-- On the left tagged factor, the normalized carrier equivalence
remembers exactly the same literal raw host vertex as the inverse
finite split equivalence. This is a statement about underlying
vertices and does not identify different codes with equal coordinates. -/
theorem RawC0CoordinateVertex.normalizedUnion_leftTag_val
    (s t : Finset RawC0CoordinateVertex)
    (hi : Function.Injective (RawC0CoordinateVertex.overlapLeft s t))
    (u : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail (RawC0CoordinateVertex.overlapLeft s t)) :
    ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
      (TaggedAmalgam.leftTag u)).val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapLeft s t) hi u).val := by
  cases u with
  | inl p =>
      change p.val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapLeft s t) hi (.inl p)).val
      rw [FiniteSpan.splitEquiv_inl]
      rfl
  | inr l =>
      change l.val.val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapLeft s t) hi (.inr l)).val
      rw [FiniteSpan.splitEquiv_inr]

/-- The same exact vertex comparison on the right tagged factor. -/
theorem RawC0CoordinateVertex.normalizedUnion_rightTag_val
    (s t : Finset RawC0CoordinateVertex)
    (hj : Function.Injective (RawC0CoordinateVertex.overlapRight s t))
    (u : {q : RawC0CoordinateVertex // q ∈ s ∩ t} ⊕
      FiniteSpan.Tail (RawC0CoordinateVertex.overlapRight s t)) :
    ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
      (TaggedAmalgam.rightTag u)).val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapRight s t) hj u).val := by
  cases u with
  | inl p =>
      change p.val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapRight s t) hj (.inl p)).val
      rw [FiniteSpan.splitEquiv_inl]
      rfl
  | inr r =>
      change r.val.val =
        (FiniteSpan.splitEquiv
          (RawC0CoordinateVertex.overlapRight s t) hj (.inr r)).val
      rw [FiniteSpan.splitEquiv_inr]

/-- The full normalized left embedding commutes with the literal
inclusion S→S∪T on underlying raw host vertices. -/
theorem RawC0CoordinateVertex.normalizedUnion_left_val
    (s t : Finset RawC0CoordinateVertex) (a : s) :
    ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
      (FiniteSpan.leftAmalgamEmbedding
        (RawC0CoordinateVertex.overlapLeft s t)
        (RawC0CoordinateVertex.overlapLeft_injective s t)
        (RawC0CoordinateVertex.overlapRight s t) a)).val = a.val := by
  let i := RawC0CoordinateVertex.overlapLeft s t
  let hi := RawC0CoordinateVertex.overlapLeft_injective s t
  have h := RawC0CoordinateVertex.normalizedUnion_leftTag_val
    s t hi ((FiniteSpan.splitEquiv i hi).symm a)
  change ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
    (TaggedAmalgam.leftTag ((FiniteSpan.splitEquiv i hi).symm a))).val = a.val
  exact h.trans
    (congrArg Subtype.val ((FiniteSpan.splitEquiv i hi).apply_symm_apply a))

/-- The full normalized right embedding commutes with T→S∪T
on underlying raw host vertices. -/
theorem RawC0CoordinateVertex.normalizedUnion_right_val
    (s t : Finset RawC0CoordinateVertex) (b : t) :
    ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
      (FiniteSpan.rightAmalgamEmbedding
        (RawC0CoordinateVertex.overlapLeft s t)
        (RawC0CoordinateVertex.overlapRight s t)
        (RawC0CoordinateVertex.overlapRight_injective s t) b)).val = b.val := by
  let j := RawC0CoordinateVertex.overlapRight s t
  let hj := RawC0CoordinateVertex.overlapRight_injective s t
  have h := RawC0CoordinateVertex.normalizedUnion_rightTag_val
    s t hj ((FiniteSpan.splitEquiv j hj).symm b)
  change ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
    (TaggedAmalgam.rightTag ((FiniteSpan.splitEquiv j hj).symm b))).val = b.val
  exact h.trans
    (congrArg Subtype.val ((FiniteSpan.splitEquiv j hj).apply_symm_apply b))

/-- For a C-closed left factor, the normalized tagged embedding,
followed by the literal-union equivalence, transports its entire
finite C-value EXACTLY to the C-value induced on S∪T. -/
theorem RawC0CoordinateVertex.normalizedUnion_left_fullC
    (s t : Finset RawC0CoordinateVertex)
    (hs : RawC0CoordinateVertex.IsClosed s)
    (a : s) :
    (RawC0CoordinateVertex.valueOn s a).image
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) ∘
        FiniteSpan.leftAmalgamEmbedding
          (RawC0CoordinateVertex.overlapLeft s t)
          (RawC0CoordinateVertex.overlapLeft_injective s t)
          (RawC0CoordinateVertex.overlapRight s t)) =
      RawC0CoordinateVertex.valueOn (s ∪ t)
        ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
          (FiniteSpan.leftAmalgamEmbedding
            (RawC0CoordinateVertex.overlapLeft s t)
            (RawC0CoordinateVertex.overlapLeft_injective s t)
            (RawC0CoordinateVertex.overlapRight s t) a)) := by
  classical
  let e := RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t
  let f := FiniteSpan.leftAmalgamEmbedding
    (RawC0CoordinateVertex.overlapLeft s t)
    (RawC0CoordinateVertex.overlapLeft_injective s t)
    (RawC0CoordinateVertex.overlapRight s t)
  let incl : s → {q : RawC0CoordinateVertex // q ∈ s ∪ t} :=
    fun r => ⟨r.val, Finset.mem_union.mpr (Or.inl r.property)⟩
  have hComm : ∀ r : s, e (f r) = incl r := by
    intro r
    apply Subtype.ext
    exact RawC0CoordinateVertex.normalizedUnion_left_val s t r
  have hFun : (e ∘ f) = incl := funext hComm
  change (RawC0CoordinateVertex.valueOn s a).image (e ∘ f) =
    RawC0CoordinateVertex.valueOn (s ∪ t) (e (f a))
  rw [hFun, hComm a]
  exact RawC0CoordinateVertex.valueOn_image_of_closed_subset
    s (s ∪ t) hs Finset.subset_union_left a

/-- The symmetric complete C-value transport for a C-closed
right factor, without any matching of component rank numbers. -/
theorem RawC0CoordinateVertex.normalizedUnion_right_fullC
    (s t : Finset RawC0CoordinateVertex)
    (ht : RawC0CoordinateVertex.IsClosed t)
    (b : t) :
    (RawC0CoordinateVertex.valueOn t b).image
      ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t) ∘
        FiniteSpan.rightAmalgamEmbedding
          (RawC0CoordinateVertex.overlapLeft s t)
          (RawC0CoordinateVertex.overlapRight s t)
          (RawC0CoordinateVertex.overlapRight_injective s t)) =
      RawC0CoordinateVertex.valueOn (s ∪ t)
        ((RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t)
          (FiniteSpan.rightAmalgamEmbedding
            (RawC0CoordinateVertex.overlapLeft s t)
            (RawC0CoordinateVertex.overlapRight s t)
            (RawC0CoordinateVertex.overlapRight_injective s t) b)) := by
  classical
  let e := RawC0CoordinateVertex.normalizedAmalgamUnionEquiv s t
  let g := FiniteSpan.rightAmalgamEmbedding
    (RawC0CoordinateVertex.overlapLeft s t)
    (RawC0CoordinateVertex.overlapRight s t)
    (RawC0CoordinateVertex.overlapRight_injective s t)
  let incl : t → {q : RawC0CoordinateVertex // q ∈ s ∪ t} :=
    fun r => ⟨r.val, Finset.mem_union.mpr (Or.inr r.property)⟩
  have hComm : ∀ r : t, e (g r) = incl r := by
    intro r
    apply Subtype.ext
    exact RawC0CoordinateVertex.normalizedUnion_right_val s t r
  have hFun : (e ∘ g) = incl := funext hComm
  change (RawC0CoordinateVertex.valueOn t b).image (e ∘ g) =
    RawC0CoordinateVertex.valueOn (s ∪ t) (e (g b))
  rw [hFun, hComm b]
  exact RawC0CoordinateVertex.valueOn_image_of_closed_subset
    t (s ∪ t) ht Finset.subset_union_right b

end FiniteUnaryCoordinates
end BigHrushovski
