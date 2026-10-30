import BigHrushovski.CFSelectedBatchSubtypeMap
import BigHrushovski.CFExactOldFreshBoundary

/-!
# Induced simultaneous C_F maps with a genuinely partial old source

An old map e:S→V is defined only on the selected finite old carrier.
When S=V=∅ and U≠∅, it need not extend to a total map U→V. The
simultaneous tagged map over the old subtype is nevertheless defined.

Full inducedness of this map reduces to:
* induced adjacency on the selected old vertices,
* equivalence of the complete old-fresh boundary of each chosen block,
* equivalence of the internal fresh-fresh graph of each chosen block.

No edges join different literal fresh request tags in either tagged
level. If the target tag map is injective, the corresponding
cross-block nonedges are automatically reflected.

This is a generic inducedness criterion for the *actual partial-map
carrier*. Local boundary and internal comparisons must subsequently
be discharged by the genuine partial named-base transport.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- A simultaneous old-subtype plus selected-block map preserves and
reflects the entire graph relation under induced old and local code
comparison. This theorem needs no total function from U to V. -/
theorem selectedTargetMapSubtype_induced
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (e : SupportCarrier U S → V)
    (hOld : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (e u) (e v))
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hT : Function.Injective T)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (hBoundary : ∀ (u : SupportCarrier U S)
        (r : SelectedRequests G Allowed bound D)
        (i : Fin r.val.code.1.val),
      (levelGraph G Allowed bound).adj
        (Sum.inl u.val) (Sum.inr ⟨r.val, i⟩) ↔
      (levelGraph H AllowedV boundV).adj
        (Sum.inl (e u)) (Sum.inr ⟨T r, phi r i⟩))
    (hFresh : ∀ (r : SelectedRequests G Allowed bound D)
        (i j : Fin r.val.code.1.val),
      (levelGraph G Allowed bound).adj
        (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨r.val, j⟩) ↔
      (levelGraph H AllowedV boundV).adj
        (Sum.inr ⟨T r, phi r i⟩)
        (Sum.inr ⟨T r, phi r j⟩))
    (x y : SelectedCarrier G Allowed bound S D) :
    (levelGraph G Allowed bound).adj
      (selectedSourceMap G Allowed bound S D x)
      (selectedSourceMap G Allowed bound S D y) ↔
    (levelGraph H AllowedV boundV).adj
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi x)
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi y) := by
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          exact (levelGraph_old_iff G Allowed bound u.val v.val).trans
            ((hOld u v).trans
              (levelGraph_old_iff H AllowedV boundV (e u) (e v)).symm)
      | inr z =>
          rcases z with ⟨r, i⟩
          exact hBoundary u r i
  | inr z =>
      rcases z with ⟨r, i⟩
      cases y with
      | inl v =>
          constructor
          · intro hadj
            have hSwap : (levelGraph G Allowed bound).adj
                (Sum.inl v.val) (Sum.inr ⟨r.val, i⟩) :=
              (levelGraph G Allowed bound).symm _ _ hadj
            exact (levelGraph H AllowedV boundV).symm _ _
              ((hBoundary v r i).mp hSwap)
          · intro hadj
            have hSwap : (levelGraph H AllowedV boundV).adj
                (Sum.inl (e v)) (Sum.inr ⟨T r, phi r i⟩) :=
              (levelGraph H AllowedV boundV).symm _ _ hadj
            exact (levelGraph G Allowed bound).symm _ _
              ((hBoundary v r i).mpr hSwap)
      | inr z' =>
          rcases z' with ⟨s, j⟩
          by_cases hrs : r = s
          · subst s
            exact hFresh r i j
          · have hSrc :
                ¬ (levelGraph G Allowed bound).adj
                  (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨s.val, j⟩) :=
              levelGraph_no_cross_fresh G Allowed bound
                r.val s.val (fun eq => hrs (Subtype.ext eq)) i j
            have hTNe : T r ≠ T s := fun eq => hrs (hT eq)
            have hDst :
                ¬ (levelGraph H AllowedV boundV).adj
                  (Sum.inr ⟨T r, phi r i⟩)
                  (Sum.inr ⟨T s, phi s j⟩) :=
              levelGraph_no_cross_fresh H AllowedV boundV
                (T r) (T s) hTNe (phi r i) (phi s j)
            exact iff_of_false hSrc hDst

end CFStageCatalogue
end BigHrushovski
