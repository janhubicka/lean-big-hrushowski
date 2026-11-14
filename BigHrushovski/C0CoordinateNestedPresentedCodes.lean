import BigHrushovski.C0CoordinateRawC0Witness

/-!
# Closure under generated restrictions of finite presented C₀ codes

Suppose a complete pointed coordinate code comes from the canonical
one-generated closure C(a) in a finite C₀ presentation. Every vertex
b in C(a) has a smaller one-generated closure C(b) ⊆ C(a).

Restricting the complete code of C(a) to the *literal coordinate
image* of C(b), and changing the distinguished point to e(b), gives
EXACTLY the complete code of C(b). In particular this retains all
graph pairs, nonedges and full set-valued unary incidences.

The argument uses the same original finite presentation for both
codes. It does not invent a new component enumeration or presuppose
that the chosen ordered local catalogue has been constructed.

The resulting property is an initial closure requirement for the
code-based coordinate host W. The final permitted ordered age and
its return embedding remain open.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The literal increasing-coordinate support of C(a), in the same
finite presentation used by the pointed code. -/
noncomputable def FiniteChronologicalC0.coordinateSupport
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) : Finset ℕ :=
  (FiniteC0.canonicalValue p.graph p.component a).image e

@[simp] theorem FiniteChronologicalC0.generatedCode_support
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.generatedCode e a).support = p.coordinateSupport e a := rfl

@[simp] theorem FiniteChronologicalC0.generatedCode_point
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.generatedCode e a).point = e a := rfl

theorem FiniteChronologicalC0.coordinateSupport_point_mem
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    e a ∈ p.coordinateSupport e a := by
  classical
  exact Finset.mem_image.mpr
    ⟨a, FiniteC0.canonicalValue_mem_self p.graph p.component a, rfl⟩

/-- Complete canonical C₀ values are nested; an increasing embedding
preserves the nesting of their literal coordinate supports. -/
theorem FiniteChronologicalC0.coordinateSupport_nested
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m)
    (hb : b ∈ FiniteC0.canonicalValue p.graph p.component a) :
    p.coordinateSupport e b ⊆ p.coordinateSupport e a := by
  classical
  intro x hx
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr
    ⟨v, FiniteC0.canonicalValue_mem_trans p.graph p.component hb hv, hvx⟩

/-- Restricting the full pointed code of C(a) to the exact coordinate
support of C(b) equals the independently coded complete C(b),
including all edges/nonedges and all positive/negative C-incidences.
The root changes from e(a) to e(b); it need not be a top generator. -/
theorem FiniteChronologicalC0.generatedCode_restrict_nested
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m)
    (hb : b ∈ FiniteC0.canonicalValue p.graph p.component a) :
    (p.generatedCode e a).restrictTo (p.coordinateSupport e b)
      (by
        rw [p.generatedCode_support]
        exact p.coordinateSupport_nested e a b hb)
      (e b) (p.coordinateSupport_point_mem e b) =
        p.generatedCode e b := by
  classical
  have hSub := p.coordinateSupport_nested e a b hb
  apply LiteralPointedCode.ext
  · rfl
  · rfl
  · change
      ((coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a)).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e b ∧
          xy.2 ∈ p.coordinateSupport e b) =
      (coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e b ∧
          xy.2 ∈ p.coordinateSupport e b)
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, _, _⟩, hb1, hb2⟩
      exact ⟨h, hb1, hb2⟩
    · rintro ⟨h, hb1, hb2⟩
      exact ⟨⟨h, hSub hb1, hSub hb2⟩, hb1, hb2⟩
  · change
      ((coordinateClosurePairs
        (FiniteC0.canonicalValue p.graph p.component) e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a)).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e b ∧
          xy.2 ∈ p.coordinateSupport e b) =
      (coordinateClosurePairs
        (FiniteC0.canonicalValue p.graph p.component) e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e b ∧
          xy.2 ∈ p.coordinateSupport e b)
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, _, _⟩, hb1, hb2⟩
      exact ⟨h, hb1, hb2⟩
    · rintro ⟨h, hb1, hb2⟩
      exact ⟨⟨h, hSub hb1, hSub hb2⟩, hb1, hb2⟩

/-- Within a given generated C₀ code, each vertex coordinate has a
root-generated, well-supported induced subcode from the SAME original
presentation. No independent choice of the resulting root is made. -/
theorem FiniteChronologicalC0.generatedCode_has_child
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m)
    (hb : b ∈ FiniteC0.canonicalValue p.graph p.component a) :
    ∃ (s : Finset ℕ)
      (hs : s ⊆ (p.generatedCode e a).support)
      (hx : e b ∈ s),
      (p.generatedCode e a).restrictTo s hs (e b) hx =
        p.generatedCode e b ∧
      (p.generatedCode e b).IsGeneratedByPoint ∧
      (p.generatedCode e b).WellSupported := by
  refine ⟨p.coordinateSupport e b, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p.generatedCode_support]
    exact p.coordinateSupport_nested e a b hb
  · exact p.coordinateSupport_point_mem e b
  · exact p.generatedCode_restrict_nested e a b hb
  · exact p.generatedCode_root e b
  · exact p.generatedCode_wellSupported e b

/-- The class of RAW finitely presented one-generated C₀ codes is
closed under one-generated restrictions of its own vertices: the
smaller code again has a concrete finite C₀ witness. This is a
witnessed existence statement, not yet a canonical child-support
function on ALL raw records. -/
theorem LiteralPointedCode.rawC0Generated_has_child
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated)
    (x : ℕ) (hx : x ∈ q.support) :
    ∃ (r : LiteralPointedCode),
      r.IsRawC0Generated ∧ r.point = x ∧
      ∃ (s : Finset ℕ) (hs : s ⊆ q.support)
        (hxs : x ∈ s), q.restrictTo s hs x hxs = r := by
  rcases hq with ⟨m, levels, p, e, a, hq⟩
  subst q
  rw [p.generatedCode_support] at hx
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
  subst x
  refine ⟨p.generatedCode e b, ⟨m, levels, p, e, b, rfl⟩, ?_,
    p.coordinateSupport e b, ?_, ?_, ?_⟩
  · exact p.generatedCode_point e b
  · rw [p.generatedCode_support]
    exact p.coordinateSupport_nested e a b hb
  · exact p.coordinateSupport_point_mem e b
  · exact p.generatedCode_restrict_nested e a b hb

end FiniteUnaryCoordinates
end BigHrushovski
