import BigHrushovski.C0CoordinateRawHostUnaryClosure

/-!
# Graph reconstruction on the preliminary raw C₀ coordinate host

Each raw coordinate vertex is a full finite pointed code of an actual
one-generated closure. Its complete adjacency matrix is symmetric and
loopless, because it was induced from a finite simple graph.

We use these matrices to define an undirected graph on the raw host:
a pair is adjacent when one pointed code is a generated child of the
other and their two coordinates form an edge in that code.

The named operation J(q) lists the neighbours of q within C(q).
We show that the entire raw graph is recovered from the two J-values,
exactly as for a graph whose edges are covered by full unary closures.

These results do not yet show that the resulting raw host has the
correct finite C₀ age, selected local orders, or the return map to
the countable generic. They are finite-code consistency lemmas.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- Complete edge-pair matrices from a finite simple graph are
symmetric. This is true even when their natural-number support is
not an interval. -/
theorem coordinateAdjacencyPairs_symm
    (G : GraphOn U) (e : U ↪o ℕ) (x y : ℕ)
    (h : (x,y) ∈ coordinateAdjacencyPairs G e) :
    (y,x) ∈ coordinateAdjacencyPairs G e := by
  classical
  unfold coordinateAdjacencyPairs at h ⊢
  obtain ⟨⟨u,v⟩, hp, heq⟩ := Finset.mem_image.mp h
  have hu : e u = x := congrArg Prod.fst heq
  have hv : e v = y := congrArg Prod.snd heq
  refine Finset.mem_image.mpr ⟨(v,u), ?_, ?_⟩
  · exact Finset.mem_filter.mpr
      ⟨by simp, G.symm u v (Finset.mem_filter.mp hp).2⟩
  · change (e v,e u) = (y,x)
    exact Prod.ext hv hu

/-- There are no diagonal edges in the full coordinate matrix of
a finite simple graph. -/
theorem coordinateAdjacencyPairs_irrefl
    (G : GraphOn U) (e : U ↪o ℕ) (x : ℕ) :
    (x,x) ∉ coordinateAdjacencyPairs G e := by
  classical
  intro h
  unfold coordinateAdjacencyPairs at h
  obtain ⟨⟨u,v⟩, hp, heq⟩ := Finset.mem_image.mp h
  have hu : e u = x := congrArg Prod.fst heq
  have hv : e v = x := congrArg Prod.snd heq
  have huv : u = v := e.injective (hu.trans hv.symm)
  have hAdj : G.adj u v := (Finset.mem_filter.mp hp).2
  exact G.irrefl u (by simpa only [huv] using hAdj)

/-- Any actual raw C₀ code has symmetric complete adjacency
incidences; well-supportedness alone would not imply this. -/
theorem LiteralPointedCode.rawC0Generated_adj_symm
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated)
    (x y : ℕ) (h : (x,y) ∈ q.adjacencyPairs) :
    (y,x) ∈ q.adjacencyPairs := by
  classical
  rcases hq with ⟨m, levels, p, e, a, hq⟩
  subst q
  change (x,y) ∈
      (coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a) at h
  obtain ⟨hEdge,hx,hy⟩ := Finset.mem_filter.mp h
  change (y,x) ∈
      (coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a)
  exact Finset.mem_filter.mpr
    ⟨coordinateAdjacencyPairs_symm p.graph e x y hEdge,hy,hx⟩

/-- No actual generated C₀ coordinate code contains a diagonal
adjacency pair. -/
theorem LiteralPointedCode.rawC0Generated_adj_irrefl
    (q : LiteralPointedCode) (hq : q.IsRawC0Generated)
    (x : ℕ) : (x,x) ∉ q.adjacencyPairs := by
  classical
  rcases hq with ⟨m, levels, p, e, a, hq⟩
  subst q
  intro h
  change (x,x) ∈
      (coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a) at h
  exact coordinateAdjacencyPairs_irrefl p.graph e x
    ((Finset.mem_filter.mp h).1)

/-- Adjacent raw code vertices must occur together in at least
one of their two complete one-generated unary values. The graph
does not identify all vertices sharing the same coordinate. -/
def RawC0CoordinateVertex.IsAdjacent
    (q r : RawC0CoordinateVertex) : Prop :=
  (r ∈ q.closedValue ∧
    (q.val.point,r.val.point) ∈ q.val.adjacencyPairs) ∨
  (q ∈ r.closedValue ∧
    (q.val.point,r.val.point) ∈ r.val.adjacencyPairs)

/-- The raw host has a well-defined simple undirected graph.
Positive and negative incidences remain encoded in complete codes. -/
noncomputable def rawC0HostGraph : GraphOn RawC0CoordinateVertex where
  adj q r := q.IsAdjacent r
  symm q r h := by
    rcases h with h | h
    · right
      exact ⟨h.1, q.val.rawC0Generated_adj_symm
        q.property q.val.point r.val.point h.2⟩
    · left
      exact ⟨h.1, r.val.rawC0Generated_adj_symm
        r.property q.val.point r.val.point h.2⟩
  irrefl q h := by
    rcases h with h | h
    · exact q.val.rawC0Generated_adj_irrefl
        q.property q.val.point h.2
    · exact q.val.rawC0Generated_adj_irrefl
        q.property q.val.point h.2

/-- The named back-neighbour operation J: complete graph neighbours
of q that are contained in its full generated C-value. -/
noncomputable def RawC0CoordinateVertex.backNeighbours
    (q : RawC0CoordinateVertex) : Finset RawC0CoordinateVertex := by
  classical
  exact q.closedValue.filter
    (fun r => (q.val.point,r.val.point) ∈ q.val.adjacencyPairs)

theorem RawC0CoordinateVertex.mem_backNeighbours_iff
    (q r : RawC0CoordinateVertex) :
    r ∈ q.backNeighbours ↔
      r ∈ q.closedValue ∧
      (q.val.point,r.val.point) ∈ q.val.adjacencyPairs := by
  classical
  simp [RawC0CoordinateVertex.backNeighbours]

/-- Every named back neighbour belongs to the complete unary value,
not merely a graph neighbourhood of its generator. -/
theorem RawC0CoordinateVertex.backNeighbours_subset_closedValue
    (q : RawC0CoordinateVertex) :
    q.backNeighbours ⊆ q.closedValue := by
  intro r hr
  exact (q.mem_backNeighbours_iff r).mp hr |>.1

/-- The full raw graph is recovered from the two unary back-neighbour
values. No global linear order on the raw host is assumed. -/
theorem rawC0HostGraph_adj_iff_backNeighbours
    (q r : RawC0CoordinateVertex) :
    rawC0HostGraph.adj q r ↔
      r ∈ q.backNeighbours ∨ q ∈ r.backNeighbours := by
  constructor
  · rintro (⟨hr,hEdge⟩ | ⟨hq,hEdge⟩)
    · exact Or.inl ((q.mem_backNeighbours_iff r).mpr ⟨hr,hEdge⟩)
    · right
      exact (r.mem_backNeighbours_iff q).mpr
        ⟨hq,r.val.rawC0Generated_adj_symm r.property
          q.val.point r.val.point hEdge⟩
  · rintro (hr | hq)
    · exact Or.inl ((q.mem_backNeighbours_iff r).mp hr)
    · obtain ⟨hqr,hEdge⟩ := (r.mem_backNeighbours_iff q).mp hq
      right
      exact ⟨hqr,r.val.rawC0Generated_adj_symm
        r.property r.val.point q.val.point hEdge⟩

/-- Every edge in the raw host is covered by the full unary closure
of one of its endpoints. -/
theorem rawC0HostGraph_edge_covered
    (q r : RawC0CoordinateVertex)
    (h : rawC0HostGraph.adj q r) :
    r ∈ q.closedValue ∨ q ∈ r.closedValue := by
  rcases h with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

end FiniteUnaryCoordinates
end BigHrushovski
