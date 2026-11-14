import BigHrushovski.C0CoordinateRawHostGraph
import BigHrushovski.C0CoordinateCanonicalLocalRepresentative

/-!
# Every finite canonical C₀ presentation embeds into the raw code host

Let p be a finite canonical C₀ presentation with minimal-strong
component steps. For each vertex a, form the raw host vertex given
by the complete pointed coordinate code of C(a) under one fixed
increasing natural-number assignment.

We prove that this map is injective and preserves and reflects the
complete unary closure, the reconstructed graph (including nonedges),
and its back-neighbour operation J. This establishes a concrete
finite-host occurrence lemma, not the full age identification.

It does not choose the compatible internal orders required for the
manuscript's W, or construct a return map to the countable generic.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- The pointed coordinates of the raw host codes recover the
original finite vertices under the increasing assignment. -/
theorem FiniteChronologicalC0.asRawVertex_point
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a : Fin m) :
    (p.asRawVertex e a).val.point = e a := rfl

/-- Each actual finite source vertex has a distinct raw host code,
even when several vertices generate the same unpointed closure. -/
theorem FiniteChronologicalC0.asRawVertex_injective
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) :
    Function.Injective (fun a : Fin m => p.asRawVertex e a) := by
  intro a b h
  have hPoint : e a = e b := by
    have hp := congrArg
      (fun q : RawC0CoordinateVertex => q.val.point) h
    simpa only [p.asRawVertex_point] using hp
  exact e.injective hPoint

/-- A complete generated raw host child belongs to C(a) precisely
when its original finite source vertex belongs to the genuine
canonical unary closure C(a). -/
theorem FiniteChronologicalC0.asRawVertex_mem_closedValue_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m) :
    p.asRawVertex e b ∈ (p.asRawVertex e a).closedValue ↔
      b ∈ FiniteC0.canonicalValue p.graph p.component a := by
  constructor
  · intro h
    obtain ⟨c,hc,hEq⟩ :=
      (p.mem_asRawVertex_closedValue_iff e a _).mp h
    have hLabels : e b = e c := by
      have hPoint := congrArg
        (fun q : RawC0CoordinateVertex => q.val.point) hEq
      simpa only [p.asRawVertex_point] using hPoint
    have hbc : b = c := e.injective hLabels
    simpa only [hbc] using hc
  · intro hb
    exact (p.mem_asRawVertex_closedValue_iff e a _).mpr
      ⟨b,hb,rfl⟩

/-- Every complete adjacency pair in the generated code reflects
the original finite graph relation, including nonedges. Both
coordinates must belong to the particular generated closure. -/
theorem FiniteChronologicalC0.generatedCode_adj_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a u v : Fin m)
    (hu : u ∈ FiniteC0.canonicalValue p.graph p.component a)
    (hv : v ∈ FiniteC0.canonicalValue p.graph p.component a) :
    (e u,e v) ∈ (p.generatedCode e a).adjacencyPairs ↔
      p.graph.adj u v := by
  classical
  have hU : e u ∈ p.coordinateSupport e a :=
    Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hV : e v ∈ p.coordinateSupport e a :=
    Finset.mem_image.mpr ⟨v,hv,rfl⟩
  change (e u,e v) ∈
      (coordinateAdjacencyPairs p.graph e).filter
        (fun xy : ℕ × ℕ =>
          xy.1 ∈ p.coordinateSupport e a ∧
          xy.2 ∈ p.coordinateSupport e a) ↔ _
  simp only [Finset.mem_filter, mem_coordinateAdjacencyPairs_iff,
    hU, hV, and_self, and_true]

/-- J on the raw host gives exactly the complete back-neighbour
value of the original finite canonical C₀ presentation. -/
theorem FiniteChronologicalC0.asRawVertex_backNeighbours_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m) :
    p.asRawVertex e b ∈ (p.asRawVertex e a).backNeighbours ↔
      b ∈ FiniteC0.canonicalValue p.graph p.component a ∧
        p.graph.adj a b := by
  rw [(p.asRawVertex e a).mem_backNeighbours_iff
      (p.asRawVertex e b)]
  constructor
  · rintro ⟨hb,hEdge⟩
    have hbC := (p.asRawVertex_mem_closedValue_iff e a b).mp hb
    exact ⟨hbC,
      (p.generatedCode_adj_iff e a a b
        (FiniteC0.canonicalValue_mem_self p.graph p.component a)
        hbC).mp hEdge⟩
  · rintro ⟨hbC,hAdj⟩
    exact ⟨(p.asRawVertex_mem_closedValue_iff e a b).mpr hbC,
      (p.generatedCode_adj_iff e a a b
        (FiniteC0.canonicalValue_mem_self p.graph p.component a)
        hbC).mpr hAdj⟩

/-- The raw host graph restricts on the image of every actual finite
canonical presentation to precisely its original complete graph.
The reverse implication reflects NONEDGES, not only positive edges.
The proof reuses edge coverage by the complete unary closures. -/
theorem FiniteChronologicalC0.asRawVertex_graph_adj_iff
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) (a b : Fin m) :
    rawC0HostGraph.adj (p.asRawVertex e a)
      (p.asRawVertex e b) ↔ p.graph.adj a b := by
  change
    (p.asRawVertex e b ∈ (p.asRawVertex e a).closedValue ∧
      (e a,e b) ∈ (p.generatedCode e a).adjacencyPairs) ∨
    (p.asRawVertex e a ∈ (p.asRawVertex e b).closedValue ∧
      (e a,e b) ∈ (p.generatedCode e b).adjacencyPairs) ↔
        p.graph.adj a b
  constructor
  · rintro (⟨hb,hEdge⟩ | ⟨ha,hEdge⟩)
    · have hbC := (p.asRawVertex_mem_closedValue_iff e a b).mp hb
      exact (p.generatedCode_adj_iff e a a b
        (FiniteC0.canonicalValue_mem_self p.graph p.component a)
        hbC).mp hEdge
    · have haC := (p.asRawVertex_mem_closedValue_iff e b a).mp ha
      exact (p.generatedCode_adj_iff e b a b haC
        (FiniteC0.canonicalValue_mem_self p.graph p.component b)).mp hEdge
  · intro hAdj
    rcases canonicalValue_edge_covered p.graph p.component a b hAdj with
      hbC | haC
    · left
      exact ⟨(p.asRawVertex_mem_closedValue_iff e a b).mpr hbC,
        (p.generatedCode_adj_iff e a a b
          (FiniteC0.canonicalValue_mem_self p.graph p.component a)
          hbC).mpr hAdj⟩
    · right
      exact ⟨(p.asRawVertex_mem_closedValue_iff e b a).mpr haC,
        (p.generatedCode_adj_iff e b a b haC
          (FiniteC0.canonicalValue_mem_self p.graph p.component b)).mpr hAdj⟩

/-- The finite canonical presentation is preserved exactly by the
injective raw-code map, simultaneously in its graph, complete unary
closure C, and the named back-neighbour function J. -/
theorem FiniteChronologicalC0.asRawVertex_exact_finite_occurrence
    {m levels : ℕ} (p : FiniteChronologicalC0 m levels)
    (e : Fin m ↪o ℕ) :
    Function.Injective (fun a : Fin m => p.asRawVertex e a) ∧
    (∀ a b : Fin m,
      rawC0HostGraph.adj (p.asRawVertex e a)
        (p.asRawVertex e b) ↔ p.graph.adj a b) ∧
    (∀ a b : Fin m,
      p.asRawVertex e b ∈ (p.asRawVertex e a).closedValue ↔
        b ∈ FiniteC0.canonicalValue p.graph p.component a) ∧
    (∀ a b : Fin m,
      p.asRawVertex e b ∈ (p.asRawVertex e a).backNeighbours ↔
        b ∈ FiniteC0.canonicalValue p.graph p.component a ∧
          p.graph.adj a b) := by
  exact ⟨p.asRawVertex_injective e,
    p.asRawVertex_graph_adj_iff e,
    p.asRawVertex_mem_closedValue_iff e,
    p.asRawVertex_backNeighbours_iff e⟩

end FiniteUnaryCoordinates
end BigHrushovski
