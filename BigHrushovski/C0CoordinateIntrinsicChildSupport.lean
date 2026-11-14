import BigHrushovski.C0CoordinateNestedPresentedCodes

/-!
# Intrinsic generated subcodes of finite pointed C₀ codes

The complete C-incidence matrix of a pointed code determines the
support of the one-generated subcode at EVERY coordinate x in its
support. The support is not an additional choice or part of an
unrecorded finite presentation: it is exactly the C-row of x.

For a raw code obtained from an actual finite canonical C₀
presentation, this intrinsic C-row is the literal coordinate image
of C(b) when x=e(b). The complete induced child is therefore again
a raw presented code.

This is the key finite closure interface for defining C on the
eventual coordinate host W. It does not yet establish the global
chosen ordered catalogue or the infinite return map.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The C-value at a coordinate in a complete pointed record, read
literally from its named unary-incidence pairs. -/
noncomputable def LiteralPointedCode.namedValue
    (q : LiteralPointedCode) (x : ℕ) : Finset ℕ :=
  q.support.filter (fun y => (x,y) ∈ q.closurePairs)

theorem LiteralPointedCode.mem_namedValue_iff
    (q : LiteralPointedCode) (x y : ℕ) :
    y ∈ q.namedValue x ↔
      y ∈ q.support ∧ (x,y) ∈ q.closurePairs := by
  classical
  simp [LiteralPointedCode.namedValue]

theorem LiteralPointedCode.namedValue_subset_support
    (q : LiteralPointedCode) (x : ℕ) :
    q.namedValue x ⊆ q.support := by
  intro y hy
  exact ((q.mem_namedValue_iff x y).mp hy).1

/-- The proof fields in a pointed restriction do not matter:
equality of its literal support determines the same complete
restricted record. -/
theorem LiteralPointedCode.restrictTo_support_congr
    (q : LiteralPointedCode) (s t : Finset ℕ)
    (hst : s = t)
    (hs : s ⊆ q.support) (ht : t ⊆ q.support)
    (x : ℕ) (hxs : x ∈ s) (hxt : x ∈ t) :
    q.restrictTo s hs x hxs = q.restrictTo t ht x hxt := by
  subst t
  rfl

/-- Within an actual one-generated code of C(a), the complete
C-incidence row at e(b) is precisely the literal coordinate support
of C(b), for EVERY b in C(a). In particular the smaller code support
is intrinsically determined without choosing a finite presentation. -/
theorem FiniteChronologicalC0.generatedCode_namedValue
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m)
    (hb : b ∈ FiniteC0.canonicalValue p.graph p.component a) :
    (p.generatedCode e a).namedValue (e b) =
      p.coordinateSupport e b := by
  classical
  let C : Fin m → Finset (Fin m) :=
    FiniteC0.canonicalValue p.graph p.component
  let S : Finset ℕ := p.coordinateSupport e a
  let Q : LiteralPointedCode := literalPointedCode p.graph C e a
  have hs : S ⊆ Q.support :=
    coordinateImage_subset_labelSupport e (C a)
  have ha : e a ∈ S := p.coordinateSupport_point_mem e a
  have hbS : e b ∈ S := by
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hCode (y : ℕ) :
      (e b, y) ∈ (p.generatedCode e a).closurePairs ↔
      (e b, y) ∈ coordinateClosurePairs C e ∧
        e b ∈ S ∧ y ∈ S := by
    exact Q.mem_restrictTo_closure_iff S hs (e a) ha (e b) y
  ext y
  constructor
  · intro h
    obtain ⟨hyS, hPair⟩ :=
      ((p.generatedCode e a).mem_namedValue_iff (e b) y).mp h
    rw [p.generatedCode_support] at hyS
    have hOrig : (e b, y) ∈ coordinateClosurePairs C e :=
      ((hCode y).mp hPair).1
    obtain ⟨v, hvS, hvy⟩ := Finset.mem_image.mp hyS
    have hvC : v ∈ C b :=
      (mem_coordinateClosurePairs_iff C e b v).mp (by
        simpa only [hvy] using hOrig)
    exact Finset.mem_image.mpr ⟨v, hvC, hvy⟩
  · intro h
    obtain ⟨v, hvC, hvy⟩ := Finset.mem_image.mp h
    have hvS : v ∈ C a :=
      FiniteC0.canonicalValue_mem_trans p.graph p.component hb hvC
    have hyS : y ∈ S :=
      Finset.mem_image.mpr ⟨v, hvS, hvy⟩
    have hOrig : (e b, y) ∈ coordinateClosurePairs C e := by
      have h' : (e b, e v) ∈ coordinateClosurePairs C e :=
        (mem_coordinateClosurePairs_iff C e b v).mpr hvC
      simpa only [hvy] using h'
    have hPair : (e b, y) ∈ (p.generatedCode e a).closurePairs :=
      (hCode y).mpr ⟨hOrig, hbS, hyS⟩
    apply ((p.generatedCode e a).mem_namedValue_iff (e b) y).mpr
    constructor
    · rw [p.generatedCode_support]
      exact hyS
    · exact hPair

/-- Every coordinate x in a raw canonical one-generated code has
an induced child with the EXACT intrinsic support read from the
complete C-row of x. The child has an actual finite C₀ witness,
and both its point and its full incidence matrices are fixed.

Unlike the previous existential-child result, there is no hidden
choice of the child's support: it is `q.namedValue x`. -/
theorem LiteralPointedCode.rawC0Generated_has_intrinsic_child
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated)
    (x : ℕ) (hx : x ∈ q.support) :
    ∃ (r : LiteralPointedCode),
      r.IsRawC0Generated ∧ r.point = x ∧
      ∃ (hxs : x ∈ q.namedValue x),
        q.restrictTo (q.namedValue x)
          (q.namedValue_subset_support x) x hxs = r := by
  rcases hq with ⟨m, levels, p, e, a, hq⟩
  subst q
  rw [p.generatedCode_support] at hx
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
  subst x
  have hN := p.generatedCode_namedValue e a b hb
  have hSelf : e b ∈ (p.generatedCode e a).namedValue (e b) := by
    rw [hN]
    exact p.coordinateSupport_point_mem e b
  refine ⟨p.generatedCode e b, ⟨m, levels, p, e, b, rfl⟩,
    p.generatedCode_point e b, hSelf, ?_⟩
  have hTS : p.coordinateSupport e b ⊆
      (p.generatedCode e a).support := by
    rw [p.generatedCode_support]
    exact p.coordinateSupport_nested e a b hb
  have hEq := (p.generatedCode e a).restrictTo_support_congr
    ((p.generatedCode e a).namedValue (e b))
    (p.coordinateSupport e b) hN
    ((p.generatedCode e a).namedValue_subset_support (e b))
    hTS (e b) hSelf (p.coordinateSupport_point_mem e b)
  exact hEq.trans (p.generatedCode_restrict_nested e a b hb)

end FiniteUnaryCoordinates
end BigHrushovski
