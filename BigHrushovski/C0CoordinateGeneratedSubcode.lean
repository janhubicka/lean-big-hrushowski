import BigHrushovski.C0CoordinatePointedSubcode

/-!
# Generated pointed subcodes from complete unary closures

A one-generated unary closure is finite and closed under all complete
unary values. Its literal coordinate set is therefore a functionally
closed support of the pointed code. The corresponding subcode records
precisely the induced graph (edges AND nonedges) and complete unary
values.

This supplies the finite incidence and closedness interface for W.
It does not prove that every such graph belongs to the finite functional
age independently of the original C0 presentation; that fact must be
taken from the finite hereditary C0 theorem at integration.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- Increasing finite labellings reflect membership in an image of a
chosen finite source subset. -/
theorem mem_coordinateImage_iff
    (e : U ↪o ℕ) (s : Finset U) (u : U) :
    e u ∈ s.image e ↔ u ∈ s := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp h
    have hVU : v = u := e.injective hEq
    simpa only [hVU] using hv
  · intro h
    exact Finset.mem_image.mpr ⟨u, h, rfl⟩

/-- The image of every finite source subset is part of the literal
coordinate support, with no unmentioned surjectivity assumption. -/
theorem coordinateImage_subset_labelSupport
    (e : U ↪o ℕ) (s : Finset U) :
    s.image e ⊆ labelSupport e := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- If a source subset is closed under the full set-valued unary
function, its literal coordinate image is a closed subcode support. -/
theorem literalPointedCode_closedImage
    (G : GraphOn U) (C : U → Finset U) (e : U ↪o ℕ)
    (root : U) (s : Finset U) (hs : ClosedUnder C s) :
    (literalPointedCode G C e root).ClosedSubset (s.image e) := by
  intro x hx y hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
  change (e u, y) ∈ coordinateClosurePairs C e at hxy
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hxy
  rcases p with ⟨a,b⟩
  have ha : a = u := e.injective (congrArg Prod.fst heq)
  have hb : e b = y := congrArg Prod.snd heq
  have hbC : b ∈ C u := by
    have hOld : b ∈ C a := (Finset.mem_filter.mp hp).2
    simpa only [ha] using hOld
  exact Finset.mem_image.mpr ⟨b, hs u hu hbC, hb⟩

/-- One-generated closures give closed coordinate supports. The
transitivity of the closure, rather than a graph-specific property,
is exactly the hypothesis needed here. -/
theorem literalPointedCode_generatedClosed
    (G : GraphOn U) (C : U → Finset U) (e : U ↪o ℕ)
    (root v : U)
    (hNested : ∀ a b : U, b ∈ C a → C b ⊆ C a) :
    (literalPointedCode G C e root).ClosedSubset ((C v).image e) := by
  apply literalPointedCode_closedImage
  intro u hu
  exact hNested v u hu

/-- A complete restricted graph code has precisely the induced
adjacency relation, including its complement. -/
theorem literalPointedCode_restrict_adj_iff
    (G : GraphOn U) (C : U → Finset U) (e : U ↪o ℕ)
    (root : U) (s : Finset U) (v : U) (hv : v ∈ s)
    (a b : U) :
    let q := literalPointedCode G C e root
    let t := s.image e
    (e a, e b) ∈ (q.restrictTo t
      (coordinateImage_subset_labelSupport e s)
      (e v) ((mem_coordinateImage_iff e s v).mpr hv)).adjacencyPairs ↔
      G.adj a b ∧ a ∈ s ∧ b ∈ s := by
  classical
  simp only [LiteralPointedCode.mem_restrictTo_adj_iff]
  rw [mem_coordinateAdjacencyPairs_iff,
      mem_coordinateImage_iff, mem_coordinateImage_iff]

/-- The restricted code also preserves AND reflects every element of
every complete unary value; no extension outside s is invented. -/
theorem literalPointedCode_restrict_closure_iff
    (G : GraphOn U) (C : U → Finset U) (e : U ↪o ℕ)
    (root : U) (s : Finset U) (v : U) (hv : v ∈ s)
    (a b : U) :
    let q := literalPointedCode G C e root
    let t := s.image e
    (e a, e b) ∈ (q.restrictTo t
      (coordinateImage_subset_labelSupport e s)
      (e v) ((mem_coordinateImage_iff e s v).mpr hv)).closurePairs ↔
      b ∈ C a ∧ a ∈ s ∧ b ∈ s := by
  classical
  simp only [LiteralPointedCode.mem_restrictTo_closure_iff]
  rw [mem_coordinateClosurePairs_iff,
      mem_coordinateImage_iff, mem_coordinateImage_iff]

end FiniteUnaryCoordinates

namespace FiniteCatalogue

open FiniteUnaryCoordinates

/-- For each vertex in a finite concrete C0 one-generated closure,
its own one-generated closure is a functionally closed subcode.
This is the concrete rooted-subcode property, not the full W theorem. -/
theorem genericC0OneGenerated_pointedSubcodeClosed
    (a : ℕ)
    (e : (genericC0UnaryClosure a) ↪o ℕ)
    (root v : genericC0UnaryClosure a) :
    (literalPointedCode
      (restrictGraph genericTwoSparseGraph (genericC0UnaryClosure a))
      (fun w => restrictValue genericC0UnaryClosure
        (genericC0UnaryClosure a) w) e root).ClosedSubset
      ((restrictValue genericC0UnaryClosure
        (genericC0UnaryClosure a) v).image e) := by
  apply literalPointedCode_generatedClosed
  intro x y hy
  exact restrictValue_nested genericC0UnaryClosure
    (genericC0UnaryClosure a)
    (fun u v h => genericC0UnaryClosure_nested h) x y hy

end FiniteCatalogue
end BigHrushovski
