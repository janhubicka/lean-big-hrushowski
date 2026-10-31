import BigHrushovski.CFPartialOldSourceCode
import BigHrushovski.CFRequestLexInjection

/-!
# Rigidity of the literal target request under partial old maps

A C_F stage request is not an abstract local isomorphism type.
Its literal named old support, fresh size, and complete ordered
adjacency matrix determine its actual request record.

This gives uniqueness of the target request built from a map
defined only on a selected old subtype. In particular the
first represented level may be mapped into an empty old stage,
even if the old source stage itself is nonempty.

The resulting theorem is the *tag rigidity* part of finite
unique level lifting. Deriving its code hypotheses from an
arbitrary embedding and proving uniqueness through several
represented levels are separate tasks.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- At a fixed old stage, literal support, fresh block size
and the complete adjacency matrix determine the entire request.
All proof-valued fields are automatically equal. -/
theorem request_eq_of_support_size_adjacency
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound)
    (hSupport : r.support = s.support)
    (hSize : r.code.1.val = s.code.1.val)
    (hCode : requestAdjacencyCode G Allowed bound r =
      requestAdjacencyCode G Allowed bound s) :
    r = s := by
  classical
  apply requestLexKey_injective G Allowed bound
  change
    (r.support.sort (· ≤ ·),
      (r.code.1.val, requestAdjacencyCode G Allowed bound r)) =
    (s.support.sort (· ≤ ·),
      (s.code.1.val, requestAdjacencyCode G Allowed bound s))
  rw [hSupport, hSize, hCode]

/-- The genuine partial-map target request is the unique target
record with the prescribed literal named support, unchanged fresh
size and unchanged entire ordered adjacency matrix. This does
not require a total function U → V. -/
theorem transportGrowthStageRequest_partial_unique
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩))
    (hClosed : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ)
    (t : StageRequest H (GrowthAllowedLocal F)
      (fun Q => K Q.card))
    (hSupport : t.support =
      CFNamedSupport.supportImage S r.support hSub e)
    (hSize : t.code.1.val = r.code.1.val)
    (hBits : requestAdjacencyCode H (GrowthAllowedLocal F)
      (fun Q => K Q.card) t =
      requestAdjacencyCode G (GrowthAllowedLocal F)
        (fun P => K P.card) r) :
    t = transportGrowthStageRequest_partial F K G H S e he
      r hSub hBase hClosed := by
  apply request_eq_of_support_size_adjacency
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
  · exact hSupport.trans
      (transportGrowthStageRequest_partial_support F K G H
        S e he r hSub hBase hClosed).symm
  · exact hSize.trans
      (transportGrowthStageRequest_partial_size F K G H
        S e he r hSub hBase hClosed).symm
  · exact hBits.trans
      (transportGrowthStageRequest_partial_adjacencyCode F K G H
        S e he r hSub hBase hClosed)

end CFStageCatalogue
end BigHrushovski
