import BigHrushovski.CFLiteralBoundaryTransport
import BigHrushovski.CFPartialOldSourceRequest

/-!
# Full old-fresh boundary under a genuinely partial old embedding

The published finite C_F lifting proof supplies an embedding of only
the selected old source S, not the entire old stage U. Its target old
stage may be empty even when U is nonempty, so no total old-stage map
U→V can be introduced.

For P⊆S, let e:S→V be injective and let P≃Q be the literal named
support equivalence induced by e. The complete old-fresh boundary of
a local graph over P is preserved and reflected by the transported
named-base graph over Q. In particular, every old vertex u in S
outside P is nonadjacent to the fresh block on both sides.

The proof needs only injectivity of e on the actual selected subtype,
not any values on U\S. All fresh-fresh bits are already handled by
the generic named-base graph theorem.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

open CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- Exact old-fresh edge and nonedge comparison after relabelling
the literal named support via a map defined *only* on S.
No extension of e to U→V is assumed. -/
theorem namedBaseGraph_partial_boundary_iff
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V)
    (he : Function.Injective e)
    (Q : Finset V)
    (iso : SupportCarrier U P ≃ SupportCarrier V Q)
    (hVal : ∀ p : SupportCarrier U P,
      (iso p).val = e ⟨p.val, hP p.property⟩)
    (n : ℕ)
    (L : GraphOn (Sum (SupportCarrier U P) (Fin n)))
    (u : SupportCarrier U S) (i : Fin n) :
    (∃ p : SupportCarrier U P,
      p.val = u.val ∧ L.adj (Sum.inl p) (Sum.inr i)) ↔
    (∃ q : SupportCarrier V Q,
      q.val = e u ∧
        (namedBaseGraph iso L).adj (Sum.inl q) (Sum.inr i)) := by
  constructor
  · rintro ⟨p, hpu, hAdj⟩
    refine ⟨iso p, ?_, ?_⟩
    · have hpU : (⟨p.val, hP p.property⟩ :
          SupportCarrier U S) = u := Subtype.ext hpu
      exact (hVal p).trans (congrArg e hpU)
    · apply (namedBaseGraph_adj_iff iso L
        (Sum.inl (iso p)) (Sum.inr i)).mpr
      simpa [namedBaseEquiv] using hAdj
  · rintro ⟨q, hqu, hAdj⟩
    let p : SupportCarrier U P := iso.symm q
    have hp : iso p = q := by simp [p]
    have hEq : e (⟨p.val, hP p.property⟩ :
          SupportCarrier U S) = e u := by
      calc
        e ⟨p.val, hP p.property⟩ = (iso p).val := (hVal p).symm
        _ = q.val := congrArg Subtype.val hp
        _ = e u := hqu
    have hpU : (⟨p.val, hP p.property⟩ :
        SupportCarrier U S) = u := he hEq
    have hpu : p.val = u.val := congrArg Subtype.val hpU
    refine ⟨p, hpu, ?_⟩
    rw [← hp] at hAdj
    have hCode := (namedBaseGraph_adj_iff iso L
      (Sum.inl (iso p)) (Sum.inr i)).mp hAdj
    simpa [namedBaseEquiv] using hCode

end CFLocalCatalogue
end BigHrushovski
