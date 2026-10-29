import BigHrushovski.CFActualNamedRequest

/-!
# The constructed named C_F request has the exact source local code

The previous module constructs an actual target StageRequest by
transporting a source request's ordered local graph along the
literal support order isomorphism. The fresh Fin ordinals are
unchanged, and no new normalization is performed.

We now identify the *complete* ordered adjacency matrices.
The proof combines the actual named-base pullback graph,
the complete sorted old-plus-fresh coordinate transport and
the generic induced adjacency-matrix theorem.

This is the missing code-equality input for applying the
partial-source request comparison and noncollision lemmas.
The simultaneous target batch remains a separate obligation.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P Q : Type*}
variable [Fintype P] [DecidableEq P] [LinearOrder P]
variable [Fintype Q] [DecidableEq Q] [LinearOrder Q]

/-- The named-base relabelling and its inverse cancel on
every local vertex, both old and fresh. -/
theorem namedBaseEquiv_sumMap
    (n : ℕ) (e : P ≃o Q) (x : Sum P (Fin n)) :
    namedBaseEquiv (B := Fin n) e.toEquiv
      (Sum.map e (OrderIso.refl (Fin n)) x) = x := by
  cases x with
  | inl p =>
      simp [namedBaseEquiv]
  | inr i =>
      simp [namedBaseEquiv]

/-- The actual transported local graph is induced along the
support order isomorphism and the identity on fresh ordinals.
All nonedges are reflected. -/
theorem namedBaseGraph_adj_orderIso
    (n : ℕ) (e : P ≃o Q)
    (G : GraphOn (Sum P (Fin n)))
    (x y : Sum P (Fin n)) :
    G.adj x y ↔
      (namedBaseGraph e.toEquiv G).adj
        (Sum.map e (OrderIso.refl (Fin n)) x)
        (Sum.map e (OrderIso.refl (Fin n)) y) := by
  change G.adj x y ↔
    G.adj
      (namedBaseEquiv (B := Fin n) e.toEquiv
        (Sum.map e (OrderIso.refl (Fin n)) x))
      (namedBaseEquiv (B := Fin n) e.toEquiv
        (Sum.map e (OrderIso.refl (Fin n)) y))
  rw [namedBaseEquiv_sumMap n e x,
    namedBaseEquiv_sumMap n e y]

end CFLocalCatalogue

namespace CFStageCatalogue

open CFLocalCatalogue

variable {P Q : Type*}
variable [Fintype P] [DecidableEq P] [LinearOrder P]
variable [Fintype Q] [DecidableEq Q] [LinearOrder Q]

/-- The full ordered adjacency matrix of a local graph is
unchanged by the canonical increasing relabelling of its
named old support, with the fresh Fin block fixed. -/
theorem namedBaseGraph_orderedAdjacencyCode
    (n : ℕ) (e : P ≃o Q)
    (G : GraphOn (Sum P (Fin n))) :
    GraphOn.orderedAdjacencyBits G
        (sortedSumCoordinates P (Fin n)) =
      GraphOn.orderedAdjacencyBits
        (namedBaseGraph e.toEquiv G)
        (sortedSumCoordinates Q (Fin n)) := by
  exact GraphOn.orderedAdjacencyBits_of_coordinate_eq
    G (namedBaseGraph e.toEquiv G)
    (Sum.map e (OrderIso.refl (Fin n)))
    (fun x y => namedBaseGraph_adj_orderIso n e G x y)
    (sortedSumCoordinates P (Fin n))
    (sortedSumCoordinates Q (Fin n))
    (sortedSumCoordinates_map_orderIso e
      (OrderIso.refl (Fin n))).symm

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The actual target request constructed from a partial old
embedding has exactly the same complete ordered adjacency
matrix as the source request. This is a statement about the
two concrete StageRequest records, not merely abstract types. -/
theorem transportGrowthStageRequest_adjacencyCode
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hClosed : H.toPredimension.IsDClosed
      (r.support.image f) Finset.univ) :
    requestAdjacencyCode G (GrowthAllowedLocal F)
      (fun P => K P.card) r =
    requestAdjacencyCode H (GrowthAllowedLocal F)
      (fun Q => K Q.card)
      (transportGrowthStageRequest F K G H S f hf
        r hSub hBase hClosed) := by
  classical
  let e := supportOrderIsoOn S r.support f hf hSub
    (r.support.image f) rfl
  change GraphOn.orderedAdjacencyBits r.code.2.graph
      (sortedSumCoordinates (SupportCarrier U r.support)
        (Fin r.code.1.val)) =
    GraphOn.orderedAdjacencyBits
      (namedBaseGraph e.toEquiv r.code.2.graph)
      (sortedSumCoordinates (SupportCarrier V (r.support.image f))
        (Fin r.code.1.val))
  exact namedBaseGraph_orderedAdjacencyCode r.code.1.val
    e r.code.2.graph

end CFStageCatalogue
end BigHrushovski
