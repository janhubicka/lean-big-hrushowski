import BigHrushovski.C0CoordinateRawHostRelabel
import BigHrushovski.C0CoordinateRawHostGraph

/-!
# Increasing coordinate maps preserve the complete raw (E,C,J) host

The raw C₀ coordinate host has complete pointed finite codes as
vertices, a simple graph E and the finite unary operations C and J.
The finite coordinate action is already known to preserve all C-values
as complete sets of pointed child codes.

We prove the missing reflection of C-membership, injectivity of the
action on ALL raw code vertices, and preservation and reflection of
the reconstructed graph and complete J-values.

All equalities use the complete graph and unary incidence matrices.
The argument does not select coherent local ordered types, identify
the eventual ordered host W, or construct its return embedding.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

/-- Applying a strictly increasing coordinate map to a full pointed
finite code is injective: the support, distinguished point, all edges
and nonedges, and all named unary incidences are reflected exactly. -/
theorem LiteralPointedCode.relabel_injective
    (h : ℕ ↪o ℕ) :
    Function.Injective (fun q : LiteralPointedCode => q.relabel h) := by
  intro q r heq
  apply LiteralPointedCode.ext
  · ext x
    have hh : h x ∈ (q.relabel h).support ↔
        h x ∈ (r.relabel h).support := by rw [heq]
    exact (mem_orderEmbedding_image_iff h q.support x).symm.trans
      (hh.trans (mem_orderEmbedding_image_iff h r.support x))
  · apply h.injective
    exact congrArg LiteralPointedCode.point heq
  · ext p
    rcases p with ⟨x,y⟩
    have hh : (h x,h y) ∈ (q.relabel h).adjacencyPairs ↔
        (h x,h y) ∈ (r.relabel h).adjacencyPairs := by rw [heq]
    exact (mem_relabel_adj_iff q h x y).symm.trans
      (hh.trans (mem_relabel_adj_iff r h x y))
  · ext p
    rcases p with ⟨x,y⟩
    have hh : (h x,h y) ∈ (q.relabel h).closurePairs ↔
        (h x,h y) ∈ (r.relabel h).closurePairs := by rw [heq]
    exact (mem_relabel_closure_iff q h x y).symm.trans
      (hh.trans (mem_relabel_closure_iff r h x y))

/-- The increasing coordinate action is injective on the WHOLE raw
host, not merely on a single generated closure. -/
theorem RawC0CoordinateVertex.relabel_injective
    (h : ℕ ↪o ℕ) :
    Function.Injective (fun q : RawC0CoordinateVertex => q.relabel h) := by
  intro q r heq
  apply Subtype.ext
  exact LiteralPointedCode.relabel_injective h
    (congrArg Subtype.val heq)

/-- Full raw C-membership is preserved and reflected, using the
injectivity of the action rather than a mere image inclusion. -/
theorem RawC0CoordinateVertex.mem_relabel_closedValue_iff
    (q r : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    r.relabel h ∈ (q.relabel h).closedValue ↔
      r ∈ q.closedValue := by
  classical
  rw [q.closedValue_relabel h]
  constructor
  · intro hr
    obtain ⟨s,hs,hsr⟩ := Finset.mem_image.mp hr
    have hEq : s = r :=
      RawC0CoordinateVertex.relabel_injective h hsr
    simpa only [hEq] using hs
  · intro hr
    exact Finset.mem_image.mpr ⟨r,hr,rfl⟩

/-- Full back-neighbour membership J is preserved and reflected.
Both graph incidence and complete C-membership are used. -/
theorem RawC0CoordinateVertex.mem_relabel_backNeighbours_iff
    (q r : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    r.relabel h ∈ (q.relabel h).backNeighbours ↔
      r ∈ q.backNeighbours := by
  constructor
  · intro hr
    obtain ⟨hC,hAdj⟩ :=
      ((q.relabel h).mem_backNeighbours_iff (r.relabel h)).mp hr
    exact (q.mem_backNeighbours_iff r).mpr
      ⟨(q.mem_relabel_closedValue_iff r h).mp hC,
        (mem_relabel_adj_iff q.val h q.val.point r.val.point).mp hAdj⟩
  · intro hr
    obtain ⟨hC,hAdj⟩ := (q.mem_backNeighbours_iff r).mp hr
    exact ((q.relabel h).mem_backNeighbours_iff (r.relabel h)).mpr
      ⟨(q.mem_relabel_closedValue_iff r h).mpr hC,
        (mem_relabel_adj_iff q.val h q.val.point r.val.point).mpr hAdj⟩

/-- The raw graph is induced by every increasing coordinate
assignment: graph edges AND nonedges are transported exactly. -/
theorem rawC0HostGraph_adj_relabel_iff
    (q r : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    rawC0HostGraph.adj (q.relabel h) (r.relabel h) ↔
      rawC0HostGraph.adj q r := by
  constructor
  · rintro (⟨hC,hAdj⟩ | ⟨hC,hAdj⟩)
    · left
      exact ⟨(q.mem_relabel_closedValue_iff r h).mp hC,
        (mem_relabel_adj_iff q.val h q.val.point r.val.point).mp hAdj⟩
    · right
      exact ⟨(r.mem_relabel_closedValue_iff q h).mp hC,
        (mem_relabel_adj_iff r.val h q.val.point r.val.point).mp hAdj⟩
  · rintro (⟨hC,hAdj⟩ | ⟨hC,hAdj⟩)
    · left
      exact ⟨(q.mem_relabel_closedValue_iff r h).mpr hC,
        (mem_relabel_adj_iff q.val h q.val.point r.val.point).mpr hAdj⟩
    · right
      exact ⟨(r.mem_relabel_closedValue_iff q h).mpr hC,
        (mem_relabel_adj_iff r.val h q.val.point r.val.point).mpr hAdj⟩

/-- The ENTIRE J-value is the image of the original J-value.
This retains the complete finite back-neighbour function. -/
theorem RawC0CoordinateVertex.backNeighbours_relabel
    [DecidableEq RawC0CoordinateVertex]
    (q : RawC0CoordinateVertex) (h : ℕ ↪o ℕ) :
    (q.relabel h).backNeighbours =
      q.backNeighbours.image (fun r => r.relabel h) := by
  classical
  ext r
  constructor
  · intro hr
    have hC : r ∈ (q.relabel h).closedValue :=
      (((q.relabel h).mem_backNeighbours_iff r).mp hr).1
    rw [q.closedValue_relabel h] at hC
    obtain ⟨s,hs,hsr⟩ := Finset.mem_image.mp hC
    have hJ : s ∈ q.backNeighbours := by
      have hJs : s.relabel h ∈ (q.relabel h).backNeighbours := by
        rw [hsr]
        exact hr
      exact (q.mem_relabel_backNeighbours_iff s h).mp hJs
    exact Finset.mem_image.mpr ⟨s,hJ,hsr⟩
  · intro hr
    obtain ⟨s,hs,hsr⟩ := Finset.mem_image.mp hr
    rw [← hsr]
    exact (q.mem_relabel_backNeighbours_iff s h).mpr hs

/-- The increasing coordinate action preserves and reflects the
complete graph, C-values and J-values simultaneously. -/
theorem rawC0Host_relabel_full_embedding
    [DecidableEq RawC0CoordinateVertex]
    (h : ℕ ↪o ℕ) :
    Function.Injective (fun q : RawC0CoordinateVertex => q.relabel h) ∧
    (∀ q r : RawC0CoordinateVertex,
      rawC0HostGraph.adj (q.relabel h) (r.relabel h) ↔
        rawC0HostGraph.adj q r) ∧
    (∀ q : RawC0CoordinateVertex,
      q.closedValue.image (fun r => r.relabel h) =
        (q.relabel h).closedValue) ∧
    (∀ q : RawC0CoordinateVertex,
      q.backNeighbours.image (fun r => r.relabel h) =
        (q.relabel h).backNeighbours) := by
  refine ⟨RawC0CoordinateVertex.relabel_injective h,
    fun q r => rawC0HostGraph_adj_relabel_iff q r h, ?_, ?_⟩
  · intro q
    exact (q.closedValue_relabel h).symm
  · intro q
    exact (q.backNeighbours_relabel h).symm

end FiniteUnaryCoordinates
end BigHrushovski
