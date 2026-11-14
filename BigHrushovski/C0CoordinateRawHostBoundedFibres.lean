import BigHrushovski.C0CoordinateRawHostFiniteClosure
import BigHrushovski.C0CoordinateBoundedSupportedFinite

/-!
# Bounded complete coordinate fibres in the raw C₀ host

Raw host vertices are actual full finite pointed C₀ codes. Although
the whole raw host is infinite, every collection of vertices whose
complete supports lie in a fixed finite interval is finite.

This is a finiteness statement about COMPLETE codes, not merely the
number of unpointed isomorphism types. In particular it distinguishes
different vertices with the same distinguished coordinate, while
keeping all graph and unary incidences.

The finite unary value of any raw host vertex lies within the same
coordinate bound as that vertex, and a finite union of such values
does not introduce new coordinates.

These are prerequisites for a component enumeration of a future W.
No order on all host vertices or countable return map is constructed.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Raw host vertices whose ENTIRE complete coordinate support lies
below the given natural bound. -/
def RawC0CoordinateVertex.Bounded (N : ℕ) : Type :=
  {q : RawC0CoordinateVertex // q.val.support ⊆ Finset.range N}

/-- Finitely many complete raw C₀ code vertices have bounded support.
The injection retains the *pointed* record including all E/C pairs,
rather than identifying codes with the same unpointed local type. -/
theorem finite_boundedRawHost (N : ℕ) :
    Finite (RawC0CoordinateVertex.Bounded N) := by
  classical
  let f : RawC0CoordinateVertex.Bounded N →
      BoundedRawC0GeneratedCode N :=
    fun q => ⟨q.val.val, ⟨q.val.property, q.property⟩⟩
  have hf : Function.Injective f := by
    intro q r heq
    have hCode : q.val.val = r.val.val :=
      congrArg (fun z : BoundedRawC0GeneratedCode N => z.val) heq
    apply Subtype.ext
    exact Subtype.ext hCode
  letI : Finite (BoundedRawC0GeneratedCode N) :=
    finite_boundedRawC0GeneratedCode N
  exact Finite.of_injective f hf

/-- Each child has support contained in its parent's full support.
This uses the intrinsic complete C-row, not graph neighbourhoods. -/
theorem RawC0CoordinateVertex.closedValue_support_subset
    (q r : RawC0CoordinateVertex)
    (hr : r ∈ q.closedValue) :
    r.val.support ⊆ q.val.support := by
  classical
  obtain ⟨x, _hx, hEq⟩ := Finset.mem_image.mp hr
  rw [← hEq, q.child_support]
  exact q.val.namedValue_subset_support x.val

/-- Every member of a one-generated complete raw C-value stays within
the same coordinate bound as its parent. -/
theorem RawC0CoordinateVertex.closedValue_bounded
    (q : RawC0CoordinateVertex) (N : ℕ)
    (hq : q.val.support ⊆ Finset.range N)
    (r : RawC0CoordinateVertex) (hr : r ∈ q.closedValue) :
    r.val.support ⊆ Finset.range N :=
  (q.closedValue_support_subset r hr).trans hq

/-- Closing a finite bounded family under the full unary operation
cannot add vertices whose coordinate supports escape the bound. -/
theorem RawC0CoordinateVertex.closeFinite_bounded
    (s : Finset RawC0CoordinateVertex) (N : ℕ)
    (hs : ∀ q ∈ s, q.val.support ⊆ Finset.range N)
    (r : RawC0CoordinateVertex)
    (hr : r ∈ RawC0CoordinateVertex.closeFinite s) :
    r.val.support ⊆ Finset.range N := by
  obtain ⟨q,hq,hqr⟩ :=
    (RawC0CoordinateVertex.mem_closeFinite_iff s r).mp hr
  exact q.closedValue_bounded N (hs q hq) r hqr

/-- The distinguished coordinate of a bounded raw host vertex is
itself below that bound. This does not make the coordinate map
injective on the whole host. -/
theorem RawC0CoordinateVertex.point_lt_of_bounded
    (q : RawC0CoordinateVertex) (N : ℕ)
    (hq : q.val.support ⊆ Finset.range N) :
    q.val.point < N :=
  Finset.mem_range.mp (hq q.val.point_mem)

end FiniteUnaryCoordinates
end BigHrushovski
