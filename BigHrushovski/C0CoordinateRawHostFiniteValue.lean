import BigHrushovski.C0CoordinateIntrinsicChildSupport

/-!
# Finite unary values on the raw C₀ coordinate-code host

Take all complete pointed finite codes realized by chronological
minimal-strong C₀ presentations. For every vertex coordinate x in
the support of such a code q, the previous theorem proves that its
C-row determines a unique complete induced child with a finite C₀
presentation witness.

This allows us to define the finite unary value C_raw(q) by listing
those child codes. Their distinguished coordinates are precisely the
support of q and are pairwise distinct.

This is a RAW coordinate host: it does not yet impose the coherent
selected local ordered-age convention, construct graph adjacency on
all host vertices, prove the whole functional closure calculus,
or yield the manuscript's W, its return embedding or Ramsey result.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- A complete raw one-generated C₀ code with an actual finite
minimal-strong presentation witness. Witnesses are propositions,
so two vertices with identical complete codes are equal. -/
def RawC0CoordinateVertex : Type :=
  {q : LiteralPointedCode // q.IsRawC0Generated}

/-- The canonical child at any coordinate x in q's support is
determined by the complete named C-row at x. Its existence follows
from the intrinsic-child theorem, without choosing a new presentation
or an arbitrary new child support. -/
noncomputable def RawC0CoordinateVertex.child
    (q : RawC0CoordinateVertex) (x : ℕ)
    (hx : x ∈ q.val.support) : RawC0CoordinateVertex := by
  classical
  let h := q.val.rawC0Generated_has_intrinsic_child q.property x hx
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- The distinguished coordinate of a child is the requested x,
not the original generating point of the parent. -/
theorem RawC0CoordinateVertex.child_point
    (q : RawC0CoordinateVertex) (x : ℕ)
    (hx : x ∈ q.val.support) :
    (q.child x hx).val.point = x := by
  classical
  exact (Classical.choose_spec
    (q.val.rawC0Generated_has_intrinsic_child q.property x hx)).2.1

/-- The child is exactly the induced pointed record on the named
unary value of x. This is independent of how q was presented. -/
theorem RawC0CoordinateVertex.child_complete_record
    (q : RawC0CoordinateVertex) (x : ℕ)
    (hx : x ∈ q.val.support) :
    ∃ (hxx : x ∈ q.val.namedValue x),
      q.val.restrictTo (q.val.namedValue x)
        (q.val.namedValue_subset_support x) x hxx =
          (q.child x hx).val := by
  classical
  exact (Classical.choose_spec
    (q.val.rawC0Generated_has_intrinsic_child q.property x hx)).2.2

/-- Each child has exactly the support prescribed by the
intrinsic complete unary C-row of the parent. -/
theorem RawC0CoordinateVertex.child_support
    (q : RawC0CoordinateVertex) (x : ℕ)
    (hx : x ∈ q.val.support) :
    (q.child x hx).val.support = q.val.namedValue x := by
  obtain ⟨hxx, hEq⟩ := q.child_complete_record x hx
  rw [← hEq]
  rfl

/-- The finite complete C-value of a raw coordinate vertex.
One child is included for every coordinate of its full support. -/
noncomputable def RawC0CoordinateVertex.closedValue
    (q : RawC0CoordinateVertex) : Finset RawC0CoordinateVertex := by
  classical
  exact (Finset.univ : Finset q.val.support).image
    (fun x : q.val.support => q.child x.val x.property)

/-- Every coordinate in the parent's support has a child in
the complete raw unary value, with exactly that distinguished
coordinate. -/
theorem RawC0CoordinateVertex.child_mem_closedValue
    (q : RawC0CoordinateVertex) (x : ℕ)
    (hx : x ∈ q.val.support) :
    q.child x hx ∈ q.closedValue := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(⟨x,hx⟩ : q.val.support), Finset.mem_univ _, rfl⟩

/-- No child in the raw unary value has its distinguished point
outside the parent's complete support. -/
theorem RawC0CoordinateVertex.closedValue_point_mem
    (q r : RawC0CoordinateVertex)
    (hr : r ∈ q.closedValue) :
    r.val.point ∈ q.val.support := by
  classical
  obtain ⟨x, _hx, hEq⟩ := Finset.mem_image.mp hr
  have hp : r.val.point = x.val := by
    rw [← hEq]
    exact q.child_point x.val x.property
  rw [hp]
  exact x.property

/-- Every coordinate of the parent occurs as the pointed coordinate
of some child in its complete finite C-value. -/
theorem RawC0CoordinateVertex.closedValue_point_surjective
    (q : RawC0CoordinateVertex)
    (x : ℕ) (hx : x ∈ q.val.support) :
    ∃ r ∈ q.closedValue, r.val.point = x := by
  exact ⟨q.child x hx, q.child_mem_closedValue x hx,
    q.child_point x hx⟩

/-- Distinct children of the SAME raw parent cannot share their
distinguished coordinate: the pointed full child code is determined
by that coordinate's C-row of the parent. This is only a local
uniqueness assertion, not the global coordinate lift into W. -/
theorem RawC0CoordinateVertex.closedValue_point_injective
    (q r s : RawC0CoordinateVertex)
    (hr : r ∈ q.closedValue) (hs : s ∈ q.closedValue)
    (hPoint : r.val.point = s.val.point) : r = s := by
  classical
  obtain ⟨x, _hx, hxr⟩ := Finset.mem_image.mp hr
  obtain ⟨y, _hy, hys⟩ := Finset.mem_image.mp hs
  have hxy : x.val = y.val := by
    calc
      x.val = (q.child x.val x.property).val.point :=
        (q.child_point x.val x.property).symm
      _ = (q.child y.val y.property).val.point := by
        rw [hxr, hys]
        exact hPoint
      _ = y.val := q.child_point y.val y.property
  have hSub : x = y := Subtype.ext hxy
  subst y
  exact hxr.symm.trans hys

/-- The raw complete unary value is nonempty, since the pointed
coordinate itself belongs to the finite support and has a child. -/
theorem RawC0CoordinateVertex.closedValue_nonempty
    (q : RawC0CoordinateVertex) : q.closedValue.Nonempty := by
  exact ⟨q.child q.val.point q.val.point_mem,
    q.child_mem_closedValue q.val.point q.val.point_mem⟩

end FiniteUnaryCoordinates
end BigHrushovski
