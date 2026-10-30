import BigHrushovski.CFPartialOldSourceRequest
import BigHrushovski.CFConstructedRequestCode

/-!
# Complete ordered code of an actual request transported by a partial map

The actual finite lifting map is defined on the selected closed
old subtype S, not on the entire old stage. Given a source request
with P⊆S, the preceding module constructs the literal target
request over Q=e[P], including when the target old stage is empty.

The target's local graph is the named-base pullback of the source
local graph under the unique increasing support isomorphism.
Since the fresh Fin ordinal is unchanged, its complete ordered
adjacency matrix agrees exactly with the source matrix:
old-old, old-fresh and fresh-fresh edges and all nonedges.

This is a direct use of the reusable
namedBaseGraph_orderedAdjacencyCode theorem, with no arbitrary
re-enumeration of the source or target supports.

The result does not yet compare different requests lexicographically
or build their simultaneous induced image.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The actual request constructed using ONLY the selected-old-source
map has exactly the source request's full ordered adjacency matrix.
This covers empty supports and empty target old stages. -/
theorem transportGrowthStageRequest_partial_adjacencyCode
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U)
    (e : SupportCarrier U S → V) (he : StrictMono e)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩))
    (hClosed : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ) :
    requestAdjacencyCode G (GrowthAllowedLocal F)
      (fun P => K P.card) r =
    requestAdjacencyCode H (GrowthAllowedLocal F)
      (fun Q => K Q.card)
      (transportGrowthStageRequest_partial F K G H
        S e he r hSub hBase hClosed) := by
  classical
  let iso := partialSupportOrderIso S r.support hSub e he
  change GraphOn.orderedAdjacencyBits r.code.2.graph
      (sortedSumCoordinates (SupportCarrier U r.support)
        (Fin r.code.1.val)) =
    GraphOn.orderedAdjacencyBits
      (CFLocalCatalogue.namedBaseGraph iso.toEquiv r.code.2.graph)
      (sortedSumCoordinates
        (SupportCarrier V
          (CFNamedSupport.supportImage S r.support hSub e))
        (Fin r.code.1.val))
  exact namedBaseGraph_orderedAdjacencyCode
    r.code.1.val iso r.code.2.graph

end CFStageCatalogue
end BigHrushovski
