import BigHrushovski.OrientationRelativeFinite
import Mathlib.Tactic

/-!
# Successor-closed sets are self-sufficient

The finite predimension argument used in Section 7 of the paper.
Each edge outside a successor-closed set has a tail outside it;
the total number of these edges is bounded by the sum of the
outdegrees of the new vertices.

This theorem does not require that the underlying graph be
2-sparse, and it does not use strict d-closure.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

/-- The unordered edges leaving a fixed vertex in the given orientation. -/
def outgoingPairs (x : V) : Finset (Finset V) :=
  (O.out x).image (fun y => ({x, y} : Finset V))

/-- An unordered edge has exactly the two displayed distinct endpoints. -/
theorem edge_eq_pair_of_adj {e : Finset V} {x y : V}
    (he : O.underlying.IsEdge e)
    (hx : x ∈ e) (hy : y ∈ e) (hxy : O.Adjacent x y) :
    e = ({x, y} : Finset V) := by
  have hxyNe : x ≠ y := by
    intro h
    subst y
    exact O.underlying.irrefl x hxy
  have hp : ({x, y} : Finset V) ⊆ e := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzx | hzy
    · subst z
      exact hx
    · have hzy' : z = y := Finset.mem_singleton.mp hzy
      subst z
      exact hy
  have hc : e.card ≤ ({x, y} : Finset V).card := by
    rw [he.1]
    simp [hxyNe]
  exact (Finset.eq_of_subset_of_card_le hp hc).symm

/-- If a directed edge of a finite set is not already inside a
successor-closed subset, its tail belongs to the new part.
No orientation root or transitive-reachability assumption is used. -/
theorem new_edge_of_arrow {s t e : Finset V} {x y : V}
    (hs : O.IsSuccessorClosed s)
    (het : e ∈ O.underlying.edgesWithin t)
    (hnot : e ∉ O.underlying.edgesWithin s)
    (hx : x ∈ e) (hy : y ∈ e)
    (hxy : y ∈ O.out x) :
    e ∈ (t \ s).biUnion O.outgoingPairs := by
  obtain ⟨heSub, heEdge⟩ := (O.underlying.mem_edgesWithin_iff t e).mp het
  have heq : e = ({x, y} : Finset V) :=
    O.edge_eq_pair_of_adj heEdge hx hy (Or.inl hxy)
  have hxNot : x ∉ s := by
    intro hxS
    have hyS : y ∈ s := hs x hxS hxy
    have heS : e ⊆ s := by
      rw [heq]
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hzy
      · subst z
        exact hxS
      · have hzy' : z = y := Finset.mem_singleton.mp hzy
        subst z
        exact hyS
    exact hnot ((O.underlying.mem_edgesWithin_iff s e).mpr ⟨heS, heEdge⟩)
  apply Finset.mem_biUnion.mpr
  refine ⟨x, Finset.mem_sdiff.mpr ⟨heSub hx, hxNot⟩, ?_⟩
  exact Finset.mem_image.mpr ⟨y, hxy, heq.symm⟩

/-- All new unordered edges belong to the union of the outgoing
edge sets of the vertices outside the closed base. -/
theorem new_edges_subset_outgoing {s t : Finset V}
    (hs : O.IsSuccessorClosed s) :
    (O.underlying.edgesWithin t \ O.underlying.edgesWithin s) ⊆
      (t \ s).biUnion O.outgoingPairs := by
  intro e he
  obtain ⟨het, hnot⟩ := Finset.mem_sdiff.mp he
  obtain ⟨_, heEdge⟩ := (O.underlying.mem_edgesWithin_iff t e).mp het
  obtain ⟨x, hx, y, hy, hadj⟩ := heEdge.2
  rcases hadj with hxy | hyx
  · exact O.new_edge_of_arrow hs het hnot hx hy hxy
  · exact O.new_edge_of_arrow hs het hnot hy hx hyx

/-- Since every new edge is assigned to its tail outside the base,
the number of new edges is at most twice the number of new vertices. -/
theorem new_edges_card_le_two {s t : Finset V}
    (hs : O.IsSuccessorClosed s) :
    (O.underlying.edgesWithin t \ O.underlying.edgesWithin s).card
      ≤ 2 * (t \ s).card := by
  have hEdges : (O.underlying.edgesWithin t \
      O.underlying.edgesWithin s).card
      ≤ ((t \ s).biUnion O.outgoingPairs).card :=
    Finset.card_le_card (O.new_edges_subset_outgoing hs)
  have hUnion : ((t \ s).biUnion O.outgoingPairs).card
      ≤ ∑ x ∈ t \ s, (O.outgoingPairs x).card :=
    Finset.card_biUnion_le
  have hImages : (∑ x ∈ t \ s, (O.outgoingPairs x).card)
      ≤ ∑ x ∈ t \ s, (O.out x).card := by
    apply Finset.sum_le_sum
    intro x hx
    exact Finset.card_image_le
  have hDegree : (∑ x ∈ t \ s, (O.out x).card)
      ≤ ∑ x ∈ t \ s, 2 := by
    apply Finset.sum_le_sum
    intro x hx
    exact O.outDegreeTwo x
  have hSum : (∑ x ∈ t \ s, 2) = 2 * (t \ s).card := by
    simp [Nat.mul_comm]
  omega

/-- The elementary predimension comparison; successor-closedness of
the base suffices, regardless of the orientation of edges inside it. -/
theorem predim_le_of_successorClosed {s t : Finset V}
    (hst : s ⊆ t) (hs : O.IsSuccessorClosed s) :
    O.underlying.predim s ≤ O.underlying.predim t := by
  have hEdgeSub : O.underlying.edgesWithin s ⊆
      O.underlying.edgesWithin t := by
    intro e he
    obtain ⟨hes, hEdge⟩ := (O.underlying.mem_edgesWithin_iff s e).mp he
    exact (O.underlying.mem_edgesWithin_iff t e).mpr
      ⟨hes.trans hst, hEdge⟩
  have hEdges := Finset.card_sdiff_add_card_eq_card hEdgeSub
  have hVertices := Finset.card_sdiff_add_card_eq_card hst
  have hBound := O.new_edges_card_le_two (t := t) hs
  unfold GraphOn.predim
  omega

/-- The manuscript's closed-strong lemma, with the complete finite
outgoing-neighbour relation and the genuine graph predimension. -/
theorem successorClosed_strong {s t : Finset V}
    (hst : s ⊆ t) (hs : O.IsSuccessorClosed s) :
    O.underlying.toPredimension.IsStrong s t := by
  refine ⟨hst, ?_⟩
  intro u hsu hut
  change O.underlying.predim s ≤ O.underlying.predim u
  exact O.predim_le_of_successorClosed hsu hs

end FiniteOrientation
end BigHrushovski
