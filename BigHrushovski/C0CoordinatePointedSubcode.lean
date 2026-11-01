import BigHrushovski.C0CoordinateLiteralCode

/-!
# Finite pointed subcodes and restrictions of complete C₀ diagrams

A pointed natural-coordinate code records its whole edge/nonedge matrix
and all members of every vertex-valued unary function. Restricting a
code to a smaller support keeps precisely the pairs with both endpoints
in the support. Functionally closed supports are singled out separately:
an arbitrary induced vertex set need not be a functional substructure.

These results do not construct the countable coordinate host W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The complete induced pointed subcode on a finite set of coordinates.
This is a record construction, not an assertion that the subset is
closed under the unary function. -/
noncomputable def LiteralPointedCode.restrictTo
    (q : LiteralPointedCode) (s : Finset ℕ)
    (_hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s) : LiteralPointedCode where
  support := s
  point := p
  point_mem := hp
  adjacencyPairs := q.adjacencyPairs.filter
    (fun xy => xy.1 ∈ s ∧ xy.2 ∈ s)
  closurePairs := q.closurePairs.filter
    (fun xy => xy.1 ∈ s ∧ xy.2 ∈ s)

@[simp] theorem LiteralPointedCode.restrictTo_support
    (q : LiteralPointedCode) (s : Finset ℕ)
    (hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s) :
    (q.restrictTo s hs p hp).support = s := rfl

@[simp] theorem LiteralPointedCode.restrictTo_point
    (q : LiteralPointedCode) (s : Finset ℕ)
    (hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s) :
    (q.restrictTo s hs p hp).point = p := rfl

/-- Exact induced adjacency and nonadjacency in the restricted code. -/
theorem LiteralPointedCode.mem_restrictTo_adj_iff
    (q : LiteralPointedCode) (s : Finset ℕ)
    (hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s)
    (x y : ℕ) :
    (x,y) ∈ (q.restrictTo s hs p hp).adjacencyPairs ↔
      (x,y) ∈ q.adjacencyPairs ∧ x ∈ s ∧ y ∈ s := by
  classical
  simp [LiteralPointedCode.restrictTo]

/-- Exact preservation of every complete unary-incidence value. -/
theorem LiteralPointedCode.mem_restrictTo_closure_iff
    (q : LiteralPointedCode) (s : Finset ℕ)
    (hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s)
    (x y : ℕ) :
    (x,y) ∈ (q.restrictTo s hs p hp).closurePairs ↔
      (x,y) ∈ q.closurePairs ∧ x ∈ s ∧ y ∈ s := by
  classical
  simp [LiteralPointedCode.restrictTo]

/-- Restriction of a restriction is the original restriction,
as an equality of COMPLETE pointed records. The new distinguished
point need not be the old one. -/
theorem LiteralPointedCode.restrictTo_restrictTo
    (q : LiteralPointedCode) (s t : Finset ℕ)
    (hs : s ⊆ q.support) (hts : t ⊆ s)
    (p : ℕ) (hp : p ∈ s)
    (v : ℕ) (hv : v ∈ t) :
    (q.restrictTo s hs p hp).restrictTo t
       (by simpa only [LiteralPointedCode.restrictTo_support] using hts)
       v hv =
      q.restrictTo t (hts.trans hs) v hv := by
  classical
  have hAdj :
      ((q.adjacencyPairs.filter (fun xy => xy.1 ∈ s ∧ xy.2 ∈ s)).
        filter (fun xy => xy.1 ∈ t ∧ xy.2 ∈ t)) =
        q.adjacencyPairs.filter (fun xy => xy.1 ∈ t ∧ xy.2 ∈ t) := by
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, _, _⟩, ht1, ht2⟩
      exact ⟨h, ht1, ht2⟩
    · rintro ⟨h, ht1, ht2⟩
      exact ⟨⟨h, hts ht1, hts ht2⟩, ht1, ht2⟩
  have hCl :
      ((q.closurePairs.filter (fun xy => xy.1 ∈ s ∧ xy.2 ∈ s)).
        filter (fun xy => xy.1 ∈ t ∧ xy.2 ∈ t)) =
        q.closurePairs.filter (fun xy => xy.1 ∈ t ∧ xy.2 ∈ t) := by
    ext xy
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, _, _⟩, ht1, ht2⟩
      exact ⟨h, ht1, ht2⟩
    · rintro ⟨h, ht1, ht2⟩
      exact ⟨⟨h, hts ht1, hts ht2⟩, ht1, ht2⟩
  cases q with
  | mk support oldPoint oldPoint_mem adj cl =>
      dsimp [LiteralPointedCode.restrictTo] at *
      rw [hAdj, hCl]

/-- A finite coordinate set closed under every named unary value.
The inclusion in the code's support is deliberately a separate input. -/
def LiteralPointedCode.ClosedSubset
    (q : LiteralPointedCode) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y, (x,y) ∈ q.closurePairs → y ∈ s

/-- Unary-closedness survives taking an intermediate induced subcode. -/
theorem LiteralPointedCode.closedSubset_of_restrictTo
    (q : LiteralPointedCode) (s t : Finset ℕ)
    (hs : s ⊆ q.support) (ht : q.ClosedSubset t)
    (hts : t ⊆ s) (p : ℕ) (hp : p ∈ s) :
    (q.restrictTo s hs p hp).ClosedSubset t := by
  intro x hx y hxy
  have hOriginal : (x,y) ∈ q.closurePairs :=
    ((q.mem_restrictTo_closure_iff s hs p hp x y).mp hxy).1
  exact ht x hx y hOriginal

end FiniteUnaryCoordinates
end BigHrushovski
