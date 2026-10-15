import BigHrushovski.CFOrderedCatalogue
import BigHrushovski.SpanNormalization
import Mathlib.Data.Finset.Sort

/-!
# Increasing normalization of ordered finite C_F extension blocks

The bounded local catalogue uses the standard increasing order on
Fin n.  An arbitrary finite linearly ordered new block B has a
*canonical increasing* enumeration by Fin(card B).

The tagged equivalence fixes the old base P literally and maps each
fresh ordinal index to the corresponding vertex of B.  Pulling
back the full graph through this equivalence retains every edge,
including edges wholly inside the new block.  Thus the indexing
does not discard the chosen order or permute the old support.

This module verifies the ordered graph normalization. Invariance of
minimal d-closedness, exact d-closed support and the concrete
growth-function class under this relabelling are separate interfaces.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P B : Type*}
variable [Fintype P] [DecidableEq P]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- Increasing enumeration of any finite linearly ordered new block. -/
noncomputable def increasingNewBlock :
    Fin (Fintype.card B) ≃o B :=
  Fintype.orderIsoFinOfCardEq B rfl

/-- The induced transport fixes every old vertex of P pointwise. -/
noncomputable def taggedIncreasingEquiv :
    Sum P (Fin (Fintype.card B)) ≃ Sum P B :=
  Equiv.sumCongr (Equiv.refl P) (increasingNewBlock (B := B)).toEquiv

@[simp] theorem taggedIncreasingEquiv_old (p : P) :
    (taggedIncreasingEquiv (P := P) (B := B)) (Sum.inl p) =
      Sum.inl p := by
  simp [taggedIncreasingEquiv]

@[simp] theorem taggedIncreasingEquiv_new
    (i : Fin (Fintype.card B)) :
    (taggedIncreasingEquiv (P := P) (B := B)) (Sum.inr i) =
      Sum.inr (increasingNewBlock (B := B) i) := by
  simp [taggedIncreasingEquiv]

/-- The original chosen linear order on B is precisely the
natural order of its fresh Fin indices. -/
theorem increasingNewBlock_lt_iff
    (i j : Fin (Fintype.card B)) :
    increasingNewBlock (B := B) i <
      increasingNewBlock (B := B) j ↔ i < j := by
  exact (increasingNewBlock (B := B)).lt_iff_lt

/-- The complete finite graph of a locally ordered extension,
relabelled without changing the old names or fresh order. -/
noncomputable def orderedNormalizeGraph (G : GraphOn (Sum P B)) :
    GraphOn (Sum P (Fin (Fintype.card B))) :=
  G.pullback (taggedIncreasingEquiv (P := P) (B := B))

theorem orderedNormalizeGraph_adj_iff
    (G : GraphOn (Sum P B))
    (u v : Sum P (Fin (Fintype.card B))) :
    (orderedNormalizeGraph G).adj u v ↔
      G.adj (taggedIncreasingEquiv (P := P) (B := B) u)
        (taggedIncreasingEquiv (P := P) (B := B) v) :=
  Iff.rfl

/-- Every adjacency within the named base remains unchanged. -/
theorem orderedNormalizeGraph_old_adj
    (G : GraphOn (Sum P B)) (p q : P) :
    (orderedNormalizeGraph G).adj (Sum.inl p) (Sum.inl q) ↔
      G.adj (Sum.inl p) (Sum.inl q) := by
  simpa only [orderedNormalizeGraph_adj_iff,
    taggedIncreasingEquiv_old]

/-- Full edges inside the fresh ordered block, not merely the
edges from the block into the old support, are preserved. -/
theorem orderedNormalizeGraph_fresh_adj
    (G : GraphOn (Sum P B))
    (i j : Fin (Fintype.card B)) :
    (orderedNormalizeGraph G).adj (Sum.inr i) (Sum.inr j) ↔
      G.adj (Sum.inr (increasingNewBlock (B := B) i))
        (Sum.inr (increasingNewBlock (B := B) j)) := by
  simpa only [orderedNormalizeGraph_adj_iff,
    taggedIncreasingEquiv_new]

/-- Boundary edges have the same old endpoint and the increasing
ordinal index of the fresh endpoint. -/
theorem orderedNormalizeGraph_boundary_adj
    (G : GraphOn (Sum P B))
    (p : P) (i : Fin (Fintype.card B)) :
    (orderedNormalizeGraph G).adj (Sum.inl p) (Sum.inr i) ↔
      G.adj (Sum.inl p)
        (Sum.inr (increasingNewBlock (B := B) i)) := by
  simpa only [orderedNormalizeGraph_adj_iff,
    taggedIncreasingEquiv_old, taggedIncreasingEquiv_new]

end CFLocalCatalogue
end BigHrushovski
