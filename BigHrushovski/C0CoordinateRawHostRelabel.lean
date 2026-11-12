import BigHrushovski.C0CoordinateRawHostUnaryClosure
import BigHrushovski.C0CoordinateCodeRelabelling

/-!
# Increasing coordinate relabellings on the preliminary raw C₀ host

An increasing injection h : ℕ ↪o ℕ acts on complete literal codes
by applying h to their support, pointed coordinate and all complete
graph/unary incidence pairs.

The class of codes realized by finite canonical C₀ presentations is
stable under this action: replace the original increasing coordinate
assignment e by e followed by h. The raw unary value commutes exactly
with this relabelling, because each child comes from the SAME finite
presentation and the complete induced-code comparison is canonical.

This does not identify the raw host with the manuscript's ordered W,
nor prove an order-compatible return map or a Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- Reassigning increasing coordinates commutes with the complete
finite graph matrix, including both orientations and absent pairs. -/
theorem coordinateAdjacencyPairs_relabel
    (G : GraphOn U) (e : U ↪o ℕ) (h : ℕ ↪o ℕ) :
    (coordinateAdjacencyPairs G e).image (relabelPair h) =
      coordinateAdjacencyPairs G (e.trans h) := by
  classical
  simp [coordinateAdjacencyPairs, Finset.image_image,
    relabelPair, Function.comp_def]

/-- The same equality for the COMPLETE finite C-incidence matrix. -/
theorem coordinateClosurePairs_relabel
    (C : U → Finset U) (e : U ↪o ℕ) (h : ℕ ↪o ℕ) :
    (coordinateClosurePairs C e).image (relabelPair h) =
      coordinateClosurePairs C (e.trans h) := by
  classical
  simp [coordinateClosurePairs, Finset.image_image,
    relabelPair, Function.comp_def]

/-- Reassigning coordinates before or after forming the whole
pointed source code gives exactly the same complete record. -/
theorem literalPointedCode_relabel
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (u : U) (h : ℕ ↪o ℕ) :
    (literalPointedCode G C e u).relabel h =
      literalPointedCode G C (e.trans h) u := by
  classical
  apply LiteralPointedCode.ext
  · simp [LiteralPointedCode.relabel, literalPointedCode,
      labelSupport, Finset.image_image, Function.comp_def]
  · rfl
  · exact coordinateAdjacencyPairs_relabel G e h
  · exact coordinateClosurePairs_relabel C e h

/-- The one-generated code of C(a) relabels exactly as the original
full finite presentation relabels. No extra local representative is
chosen or named top generator introduced. -/
theorem FiniteChronologicalC0.generatedCode_relabel
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) (h : ℕ ↪o ℕ) :
    (p.generatedCode e a).relabel h =
      p.generatedCode (e.trans h) a := by
  classical
  let C := FiniteC0.canonicalValue p.graph p.component
  let s := (C a).image e
  have hs : s ⊆ (literalPointedCode p.graph C e a).support :=
    coordinateImage_subset_labelSupport e (C a)
  have hv : e a ∈ s :=
    (mem_coordinateImage_iff e (C a) a).mpr
      (FiniteC0.canonicalValue_mem_self p.graph p.component a)
  have hs' : s.image h ⊆
      ((literalPointedCode p.graph C e a).relabel h).support := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨y,hs hy,rfl⟩
  have hv' : h (e a) ∈ s.image h :=
    Finset.mem_image.mpr ⟨e a,hv,rfl⟩
  have hCode :
      (p.generatedCode e a).relabel h =
      ((literalPointedCode p.graph C e a).relabel h).restrictTo
        (s.image h) hs' (h (e a)) hv' := by
    exact (literalPointedCode p.graph C e a).relabel_restrictTo
      h s hs (e a) hv
  have hSupport : s.image h = (C a).image (e.trans h) := by
    classical
    simp [s, Finset.image_image, Function.comp_def]
  change (p.generatedCode e a).relabel h =
    (literalPointedCode p.graph C (e.trans h) a).restrictTo
      ((C a).image (e.trans h))
      (coordinateImage_subset_labelSupport (e.trans h) (C a))
      ((e.trans h) a)
      ((mem_coordinateImage_iff (e.trans h) (C a) a).mpr
        (FiniteC0.canonicalValue_mem_self p.graph p.component a))
  simpa only [literalPointedCode_relabel, hSupport] using hCode

/-- Increasing coordinate maps preserve the class of raw codes
admitting an actual finite minimal-strong C₀ presentation. -/
theorem LiteralPointedCode.rawC0Generated_relabel
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated)
    (h : ℕ ↪o ℕ) : (q.relabel h).IsRawC0Generated := by
  rcases hq with ⟨m, levels, p, e, a, hq⟩
  subst q
  exact ⟨m, levels, p, e.trans h, a,
    p.generatedCode_relabel e a h⟩

/-- The increasing-coordinate action on raw coordinate-host
vertices, using the complete relabelled record and an actual
finite presentation witness. -/
noncomputable def RawC0CoordinateVertex.relabel
    (q : RawC0CoordinateVertex)
    (h : ℕ ↪o ℕ) : RawC0CoordinateVertex :=
  ⟨q.val.relabel h,
    q.val.rawC0Generated_relabel q.property h⟩

@[simp] theorem RawC0CoordinateVertex.relabel_point
    (q : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    (q.relabel h).val.point = h q.val.point := rfl

@[simp] theorem RawC0CoordinateVertex.relabel_support
    (q : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    (q.relabel h).val.support = q.val.support.image h := rfl

/-- Reassigning all coordinates of a presented one-generated
closure is exactly the same as reassigning the embedding of its
finite source carrier. -/
theorem FiniteChronologicalC0.asRawVertex_relabel
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) (h : ℕ ↪o ℕ) :
    (p.asRawVertex e a).relabel h =
      p.asRawVertex (e.trans h) a := by
  apply Subtype.ext
  exact p.generatedCode_relabel e a h

/-- The full finite unary C-value of a raw coordinate vertex
commutes with EVERY increasing reassignment of its coordinates.
In particular all complete child codes, not only their pointed
coordinates, are transported. -/
theorem RawC0CoordinateVertex.closedValue_relabel
    [DecidableEq RawC0CoordinateVertex]
    (q : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    (q.relabel h).closedValue =
      q.closedValue.image (fun r => r.relabel h) := by
  classical
  rcases q with ⟨code, hcode⟩
  rcases hcode with ⟨m, levels, p, e, a, hEq⟩
  subst code
  change ((p.asRawVertex e a).relabel h).closedValue =
    (p.asRawVertex e a).closedValue.image
      (fun r => r.relabel h)
  rw [p.asRawVertex_relabel e a h]
  ext r
  constructor
  · intro hr
    obtain ⟨b,hb,hrEq⟩ :=
      (p.mem_asRawVertex_closedValue_iff (e.trans h) a r).mp hr
    have hPresent : p.asRawVertex e b ∈
        (p.asRawVertex e a).closedValue :=
      (p.mem_asRawVertex_closedValue_iff e a _).mpr ⟨b,hb,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨p.asRawVertex e b, hPresent, ?_⟩
    rw [hrEq]
    exact p.asRawVertex_relabel e b h
  · intro hr
    obtain ⟨s,hs,hsr⟩ := Finset.mem_image.mp hr
    obtain ⟨b,hb,hsEq⟩ :=
      (p.mem_asRawVertex_closedValue_iff e a s).mp hs
    apply (p.mem_asRawVertex_closedValue_iff (e.trans h) a r).mpr
    refine ⟨b,hb,?_⟩
    rw [hsEq] at hsr
    exact hsr.symm.trans (p.asRawVertex_relabel e b h)

end FiniteUnaryCoordinates
end BigHrushovski
