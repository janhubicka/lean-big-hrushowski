import BigHrushovski.C0CoordinateRawHostFiniteValue

/-!
# Reflexivity and nestedness of unary values on the raw coordinate host

The raw coordinate host consists of complete pointed codes obtained
from one-generated closures in finite canonical C₀ presentations.
Its finite unary value is the collection of all generated child
codes, one for each coordinate of the parent's support.

We prove that these values are reflexive and nested. The argument
compares all children with the same original finite presentation;
it reuses exact induced-code equality instead of introducing another
closure calculation. The conclusions are independent of a choice of
presentation because the code of each child is intrinsic to its parent.

The full ordered coordinate host W still requires the hereditary
selection of locally ordered types, graph reconstruction, and the
return embedding. No such assertion is made here.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Regard one one-generated closure in an actual finite canonical
presentation as a vertex of the raw coordinate host. -/
noncomputable def FiniteChronologicalC0.asRawVertex
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) : RawC0CoordinateVertex :=
  ⟨p.generatedCode e a, ⟨m, levels, p, e, a, rfl⟩⟩

@[simp] theorem FiniteChronologicalC0.asRawVertex_val
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.asRawVertex e a).val = p.generatedCode e a := rfl

/-- The raw child's complete code agrees with the code of the smaller
one-generated closure in the SAME original finite presentation.
Its support and ALL E/C incidences are preserved. -/
theorem FiniteChronologicalC0.asRawVertex_child
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m)
    (hb : b ∈ FiniteC0.canonicalValue p.graph p.component a)
    (hx : e b ∈ (p.asRawVertex e a).val.support) :
    (p.asRawVertex e a).child (e b) hx = p.asRawVertex e b := by
  apply Subtype.ext
  obtain ⟨hxx, hEq⟩ :=
    (p.asRawVertex e a).child_complete_record (e b) hx
  have hRow :
      (p.generatedCode e a).namedValue (e b) =
        p.coordinateSupport e b :=
    p.generatedCode_namedValue e a b hb
  have hSub : p.coordinateSupport e b ⊆
      (p.generatedCode e a).support := by
    rw [p.generatedCode_support]
    exact p.coordinateSupport_nested e a b hb
  have hCon := (p.generatedCode e a).restrictTo_support_congr
    ((p.generatedCode e a).namedValue (e b))
    (p.coordinateSupport e b) hRow
    ((p.generatedCode e a).namedValue_subset_support (e b))
    hSub (e b) hxx (p.coordinateSupport_point_mem e b)
  calc
    ((p.asRawVertex e a).child (e b) hx).val =
        (p.generatedCode e a).restrictTo
          ((p.generatedCode e a).namedValue (e b))
          ((p.generatedCode e a).namedValue_subset_support (e b))
          (e b) hxx := hEq.symm
    _ = (p.generatedCode e a).restrictTo
          (p.coordinateSupport e b) hSub
          (e b) (p.coordinateSupport_point_mem e b) := hCon
    _ = p.generatedCode e b :=
      p.generatedCode_restrict_nested e a b hb

/-- The finite unary value of a presented raw vertex consists
EXACTLY of all one-generated codes of points in its original C-value.
This is an equality of actual host vertices, not merely of coordinates. -/
theorem FiniteChronologicalC0.mem_asRawVertex_closedValue_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m)
    (r : RawC0CoordinateVertex) :
    r ∈ (p.asRawVertex e a).closedValue ↔
      ∃ b : Fin m,
        b ∈ FiniteC0.canonicalValue p.graph p.component a ∧
          r = p.asRawVertex e b := by
  classical
  constructor
  · intro hr
    obtain ⟨x, _, hxr⟩ := Finset.mem_image.mp hr
    rcases x with ⟨x, hx⟩
    change x ∈ (p.generatedCode e a).support at hx
    rw [p.generatedCode_support] at hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨b, hb, ?_⟩
    exact hxr.symm.trans
      (p.asRawVertex_child e a b hb _)
  · rintro ⟨b, hb, rfl⟩
    have hx : e b ∈ (p.asRawVertex e a).val.support := by
      change e b ∈ p.coordinateSupport e a
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    rw [← p.asRawVertex_child e a b hb hx]
    exact (p.asRawVertex e a).child_mem_closedValue (e b) hx

/-- Reflexivity of the full raw coordinate-host unary operation.
The child at the original distinguished point is the parent itself. -/
theorem RawC0CoordinateVertex.mem_closedValue_self
    (q : RawC0CoordinateVertex) : q ∈ q.closedValue := by
  rcases q with ⟨code, hcode⟩
  rcases hcode with ⟨m, levels, p, e, a, hEq⟩
  subst code
  change p.asRawVertex e a ∈ (p.asRawVertex e a).closedValue
  apply (p.mem_asRawVertex_closedValue_iff e a _).mpr
  exact ⟨a, FiniteC0.canonicalValue_mem_self p.graph p.component a, rfl⟩

/-- Nestedness of full raw unary values. This is stronger than the
nonemptiness and coordinate uniqueness of the previous finite host:
every child of a child is already a child of the original parent. -/
theorem RawC0CoordinateVertex.closedValue_nested
    (q r : RawC0CoordinateVertex)
    (hr : r ∈ q.closedValue) :
    r.closedValue ⊆ q.closedValue := by
  rcases q with ⟨code, hcode⟩
  rcases hcode with ⟨m, levels, p, e, a, hEq⟩
  subst code
  change r ∈ (p.asRawVertex e a).closedValue at hr
  obtain ⟨b, hb, hR⟩ :=
    (p.mem_asRawVertex_closedValue_iff e a r).mp hr
  subst r
  intro s hs
  obtain ⟨c, hbc, hS⟩ :=
    (p.mem_asRawVertex_closedValue_iff e b s).mp hs
  subst s
  apply (p.mem_asRawVertex_closedValue_iff e a _).mpr
  exact ⟨c, FiniteC0.canonicalValue_mem_trans
    p.graph p.component hb hbc, rfl⟩

/-- The raw coordinate code host satisfies both basic unary closure
laws without an extra axiom of heredity for a chosen ordered catalogue. -/
theorem RawC0CoordinateVertex.closedValue_reflexive_nested :
    (∀ q : RawC0CoordinateVertex, q ∈ q.closedValue) ∧
    (∀ q r : RawC0CoordinateVertex,
      r ∈ q.closedValue → r.closedValue ⊆ q.closedValue) := by
  exact ⟨RawC0CoordinateVertex.mem_closedValue_self,
    RawC0CoordinateVertex.closedValue_nested⟩

end FiniteUnaryCoordinates
end BigHrushovski
