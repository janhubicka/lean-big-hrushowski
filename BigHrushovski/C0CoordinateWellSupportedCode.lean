import BigHrushovski.C0CoordinatePointedAgeCode
import BigHrushovski.C0CoordinatePointedSubcode

/-!
# Complete coordinate codes supported on their declared finite carriers

The general `LiteralPointedCode` record merely requires its named
point to lie in its finite support. It does NOT require the adjacency
and C-incidence pairs to have both endpoints in that support.

All codes obtained from actual finite structures satisfy the stronger
condition. It is necessary when defining the permitted-code universe
for W: without it, even support {0} allows infinitely many artificial
codes with graph pairs at arbitrarily large unrelated coordinates.

Here we make this finite-support condition explicit, verify it for
actual source codes, show that induced restrictions always satisfy it,
and derive exact coordinate bounds for complete incidence matrices.
This does not yet construct the set of permitted codes or W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Every complete edge and unary-incidence entry uses coordinates in
the actual declared finite support. Absence of entries still records
nonedges and negative C-incidences. -/
def LiteralPointedCode.WellSupported (q : LiteralPointedCode) : Prop :=
  q.adjacencyPairs ⊆ q.support.product q.support ∧
  q.closurePairs ⊆ q.support.product q.support

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- A literal coordinate code made from any finite graph and complete
finite-valued unary function has no incidence outside its support.
No C₀ admissibility or closedness hypothesis is needed here. -/
theorem literalPointedCode_wellSupported
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (root : U) :
    (literalPointedCode G C e root).WellSupported := by
  classical
  constructor
  · intro xy hxy
    change xy ∈ coordinateAdjacencyPairs G e at hxy
    obtain ⟨⟨u,v⟩, _hPair, hEq⟩ := Finset.mem_image.mp hxy
    have hu : e u = xy.1 := congrArg Prod.fst hEq
    have hv : e v = xy.2 := congrArg Prod.snd hEq
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩
  · intro xy hxy
    change xy ∈ coordinateClosurePairs C e at hxy
    obtain ⟨⟨u,v⟩, _hPair, hEq⟩ := Finset.mem_image.mp hxy
    have hu : e u = xy.1 := congrArg Prod.fst hEq
    have hv : e v = xy.2 := congrArg Prod.snd hEq
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩
    · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩

/-- A complete induced subcode has no pairs outside its new support,
even if the unrestricted parent record contained phantom pairs.
This is a RECORD property; functional closedness is separate. -/
theorem LiteralPointedCode.restrictTo_wellSupported
    (q : LiteralPointedCode) (s : Finset ℕ)
    (hs : s ⊆ q.support) (p : ℕ) (hp : p ∈ s) :
    (q.restrictTo s hs p hp).WellSupported := by
  constructor
  · intro xy hxy
    rcases xy with ⟨x,y⟩
    obtain ⟨_,hx,hy⟩ :=
      (q.mem_restrictTo_adj_iff s hs p hp x y).mp hxy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  · intro xy hxy
    rcases xy with ⟨x,y⟩
    obtain ⟨_,hx,hy⟩ :=
      (q.mem_restrictTo_closure_iff s hs p hp x y).mp hxy
    exact Finset.mem_product.mpr ⟨hx,hy⟩

/-- If the support uses coordinates < N, then ALL adjacency pairs use
two coordinates < N. This is the finite-fibre prerequisite for W. -/
theorem LiteralPointedCode.adjacencyPairs_subset_range_product
    (q : LiteralPointedCode) (hq : q.WellSupported)
    (N : ℕ) (hBound : q.support ⊆ Finset.range N) :
    q.adjacencyPairs ⊆ (Finset.range N).product (Finset.range N) := by
  intro xy hxy
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp (hq.1 hxy)
  exact Finset.mem_product.mpr ⟨hBound hx, hBound hy⟩

/-- The identical bound holds for all complete named C-incidences.
Without well-supportedness the assertion would be false. -/
theorem LiteralPointedCode.closurePairs_subset_range_product
    (q : LiteralPointedCode) (hq : q.WellSupported)
    (N : ℕ) (hBound : q.support ⊆ Finset.range N) :
    q.closurePairs ⊆ (Finset.range N).product (Finset.range N) := by
  intro xy hxy
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp (hq.2 hxy)
  exact Finset.mem_product.mpr ⟨hBound hx, hBound hy⟩

/-- Both complete matrices and the distinguished coordinate are
bounded by the finite support. This is a necessary (not sufficient)
condition for interpreting a bounded collection of local codes. -/
theorem LiteralPointedCode.wellSupported_bounded
    (q : LiteralPointedCode) (hq : q.WellSupported)
    (N : ℕ) (hBound : q.support ⊆ Finset.range N) :
    q.point ∈ Finset.range N ∧
    q.adjacencyPairs ⊆ (Finset.range N).product (Finset.range N) ∧
    q.closurePairs ⊆ (Finset.range N).product (Finset.range N) := by
  exact ⟨hBound q.point_mem,
    q.adjacencyPairs_subset_range_product hq N hBound,
    q.closurePairs_subset_range_product hq N hBound⟩

end FiniteUnaryCoordinates
end BigHrushovski
