import BigHrushovski.CFRequestLexKeys

/-!
# Complete local graph matrices for C_F request codes

The local ordered coordinates of an actual StageRequest are the
complete increasing old support followed by the complete ordered
fresh Fin block. Thus every local vertex appears in the list.

The generic finite-graph adjacency-code theorem now proves that
the request's row-major adjacency matrix distinguishes *all*
local graphs over that same named support and fresh size. It
includes edges within the fresh block and reflects nonedges.

The remaining dependent request-key injectivity step must first
use equality of support tuples and fresh sizes to identify the
two local carrier types; it can then invoke this theorem without
repeating graph-theoretic arguments.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]

/-- The ordered coordinate list of a request contains every old
support vertex and every fresh vertex. No choice of isomorphic
representatives or unordered old coordinates is involved. -/
theorem requestLocalCoordinates_complete
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound)
    (v : Sum (SupportCarrier U r.support) (Fin r.code.1.val)) :
    v ∈ requestLocalCoordinates G Allowed bound r := by
  classical
  rcases v with u | i
  · unfold requestLocalCoordinates
    apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    refine ⟨u, ?_, rfl⟩
    simp
  · unfold requestLocalCoordinates
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    simp

/-- Fix one named support and fresh size of an actual request.
The complete ordered adjacency code is then injective as a
function of the *entire* local graph on that literal carrier. -/
theorem requestLocalGraphCode_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    Function.Injective
      (fun H : GraphOn
          (Sum (SupportCarrier U r.support) (Fin r.code.1.val)) =>
        GraphOn.orderedAdjacencyBits H
          (requestLocalCoordinates G Allowed bound r)) := by
  exact GraphOn.orderedAdjacencyBits_injective_of_complete
    (requestLocalCoordinates G Allowed bound r)
    (requestLocalCoordinates_complete G Allowed bound r)

/-- The request adjacency matrix is exactly the generic complete
graph code evaluated on its own ordered local graph and its
full coordinate list. -/
theorem requestAdjacencyCode_eq_complete
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    requestAdjacencyCode G Allowed bound r =
      GraphOn.orderedAdjacencyBits r.code.2.graph
        (requestLocalCoordinates G Allowed bound r) := rfl

end CFStageCatalogue
end BigHrushovski
