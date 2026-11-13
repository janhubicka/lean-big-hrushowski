import BigHrushovski.C0CoordinateRawHostBoundedFibres
import BigHrushovski.C0CoordinatePointedTopRoots
import BigHrushovski.C0CoordinateHostGraph

/-!
# Mutual C-generation and complete code consistency in the raw host

A raw coordinate-host vertex carries a complete pointed code,
including the whole graph and set-valued unary incidence matrices.
If two such vertices belong to each other's complete unary C-values,
then their finite supports coincide. More strongly, the two complete
UNPOINTED codes coincide: the difference is only the choice of
generating root.

This extra conclusion is needed to identify the named J-value
with the actual graph neighbours INSIDE C. The previously established
graph reconstruction E(q,r) iff r in J(q) or q in J(r) does not alone
imply J(q) = N_E(q) intersect C(q).

We use exact restriction of complete code records, not agreement of
positive edges or of coordinate supports alone. This does not
construct a chosen ordered local catalogue or the manuscript's W.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Restricting a complete well-supported pointed code to its WHOLE
support and choosing another point in it changes no adjacency or
unary incidence data. In particular its full unpointed key is fixed.
Well-supportedness is necessary: phantom out-of-support pairs would
be removed by the restriction. -/
theorem LiteralPointedCode.restrictTo_full_unpointedKey
    (q : LiteralPointedCode) (hSupported : q.WellSupported)
    (x : ℕ) (hx : x ∈ q.support) :
    (q.restrictTo q.support Finset.Subset.rfl x hx).unpointedKey =
      q.unpointedKey := by
  classical
  apply (LiteralPointedCode.unpointedKey_eq_iff
    (q.restrictTo q.support Finset.Subset.rfl x hx) q).mpr
  refine ⟨rfl, ?_, ?_⟩
  · change q.adjacencyPairs.filter
      (fun xy : ℕ × ℕ =>
        xy.1 ∈ q.support ∧ xy.2 ∈ q.support) =
        q.adjacencyPairs
    ext xy
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).1
    · intro h
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hSupported.1 h)
      exact Finset.mem_filter.mpr ⟨h,h1,h2⟩
  · change q.closurePairs.filter
      (fun xy : ℕ × ℕ =>
        xy.1 ∈ q.support ∧ xy.2 ∈ q.support) =
        q.closurePairs
    ext xy
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).1
    · intro h
      obtain ⟨h1,h2⟩ := Finset.mem_product.mp (hSupported.2 h)
      exact Finset.mem_filter.mpr ⟨h,h1,h2⟩

/-- Membership of r in the full C-value of q identifies r with
the EXACT induced pointed subcode of q on the full C-row of
r's coordinate. This retains the negative E/C incidences. -/
theorem RawC0CoordinateVertex.member_complete_restriction
    (q r : RawC0CoordinateVertex)
    (hr : r ∈ q.closedValue) :
    ∃ (hx : r.val.point ∈ q.val.support)
      (hxx : r.val.point ∈ q.val.namedValue r.val.point),
      q.val.restrictTo (q.val.namedValue r.val.point)
        (q.val.namedValue_subset_support r.val.point)
        r.val.point hxx = r.val := by
  let x := r.val.point
  have hx : x ∈ q.val.support :=
    q.closedValue_point_mem r hr
  have hchild : q.child x hx = r :=
    q.closedValue_point_injective (q.child x hx) r
      (q.child_mem_closedValue x hx) hr
      (q.child_point x hx)
  obtain ⟨hxx,hEq⟩ := q.child_complete_record x hx
  refine ⟨hx,hxx,?_⟩
  rw [hchild] at hEq
  exact hEq

/-- If two raw host code vertices generate each other, their
ENTIRE complete unpointed coordinate records agree. The result
includes all edges/nonedges and all positive/negative C-incidences.
It is stronger than equality of coordinate supports. -/
theorem RawC0CoordinateVertex.mutual_closedValue_unpointedKey
    (q r : RawC0CoordinateVertex)
    (hqr : r ∈ q.closedValue) (hrq : q ∈ r.closedValue) :
    q.val.unpointedKey = r.val.unpointedKey := by
  classical
  have hS : q.val.support = r.val.support :=
    Finset.Subset.antisymm
      (r.closedValue_support_subset q hrq)
      (q.closedValue_support_subset r hqr)
  obtain ⟨hx,hxx,hRestrict⟩ :=
    q.member_complete_restriction r hqr
  have hNamed : q.val.namedValue r.val.point =
      r.val.support :=
    congrArg LiteralPointedCode.support hRestrict
  have hWhole : q.val.namedValue r.val.point =
      q.val.support := hNamed.trans hS.symm
  have hEq := q.val.restrictTo_support_congr
    (q.val.namedValue r.val.point) q.val.support hWhole
    (q.val.namedValue_subset_support r.val.point)
    Finset.Subset.rfl r.val.point hxx hx
  have hRecord :
      q.val.restrictTo q.val.support Finset.Subset.rfl
        r.val.point hx = r.val :=
    hEq.symm.trans hRestrict
  have hKey := q.val.restrictTo_full_unpointedKey
    (q.val.rawC0Generated_wellSupported q.property)
    r.val.point hx
  exact hKey.symm.trans
    (congrArg LiteralPointedCode.unpointedKey hRecord)

/-- Hence both raw adjacency matrices agree on every pair whenever
the vertices generate each other; no arbitrary choice of preferred
top generator is used. -/
theorem RawC0CoordinateVertex.mutual_closedValue_adjacency
    (q r : RawC0CoordinateVertex)
    (hqr : r ∈ q.closedValue) (hrq : q ∈ r.closedValue) :
    q.val.adjacencyPairs = r.val.adjacencyPairs :=
  ((q.val.unpointedKey_eq_iff r.val).mp
    (q.mutual_closedValue_unpointedKey r hqr hrq)).2.1

/-- The same exact equality for the entire unary C-incidence
matrix, including every negative incidence. -/
theorem RawC0CoordinateVertex.mutual_closedValue_C
    (q r : RawC0CoordinateVertex)
    (hqr : r ∈ q.closedValue) (hrq : q ∈ r.closedValue) :
    q.val.closurePairs = r.val.closurePairs :=
  ((q.val.unpointedKey_eq_iff r.val).mp
    (q.mutual_closedValue_unpointedKey r hqr hrq)).2.2

/-- Exact identification of the named raw J-value with the graph
neighbours INSIDE the full generated C-value. Unlike the earlier
graph-reconstruction identity, this requires consistency of the
complete local codes for mutual generators. -/
theorem RawC0CoordinateVertex.mem_backNeighbours_iff_graph
    (q r : RawC0CoordinateVertex) :
    r ∈ q.backNeighbours ↔
      r ∈ q.closedValue ∧ rawC0HostGraph.adj q r := by
  constructor
  · intro hr
    obtain ⟨hC,hAdj⟩ := (q.mem_backNeighbours_iff r).mp hr
    exact ⟨hC,Or.inl ⟨hC,hAdj⟩⟩
  · rintro ⟨hC,hE⟩
    change RawC0CoordinateVertex.IsAdjacent q r at hE
    rcases hE with ⟨_,hAdj⟩ | ⟨hMutual,hAdj⟩
    · exact (q.mem_backNeighbours_iff r).mpr ⟨hC,hAdj⟩
    · have hEq : q.val.adjacencyPairs = r.val.adjacencyPairs :=
        q.mutual_closedValue_adjacency r hC hMutual
      have hAdjQ : (q.val.point,r.val.point) ∈
          q.val.adjacencyPairs := by
        rw [hEq]
        exact hAdj
      exact (q.mem_backNeighbours_iff r).mpr ⟨hC,hAdjQ⟩

/-- The named J-value is precisely the ordinary back-neighbour
function of the raw graph with its COMPLETE unary closure C. -/
theorem RawC0CoordinateVertex.backNeighbours_eq_graph
    (q : RawC0CoordinateVertex) :
    q.backNeighbours =
      rawC0HostGraph.backAdjacencyValue
        RawC0CoordinateVertex.closedValue q := by
  classical
  ext r
  rw [q.mem_backNeighbours_iff_graph r,
    rawC0HostGraph.mem_backAdjacencyValue_iff
      RawC0CoordinateVertex.closedValue q r]

end FiniteUnaryCoordinates
end BigHrushovski
