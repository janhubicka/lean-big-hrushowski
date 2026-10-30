import BigHrushovski.CFSelectedBatchSubtypeMap
import BigHrushovski.CFSelectedBatchLexOrder

/-!
# Exact tagged order under a genuinely partial old-source map

The simultaneous selected carrier has old vertices from the *actual*
old subtype S and fresh blocks carrying literal request tags.
The target old stage may be empty even when the full source old
stage is nonempty, so the order proof must not totalize the old map.

The tagged comparison is precisely the manuscript comparison:
old vertices precede every fresh vertex, old vertices retain their
inherited order, and fresh vertices compare first by the complete
named support/fresh-size/ordered adjacency code of their requests,
then by their chosen natural ordinal.

We prove the exact comparison is preserved and reflected under a
strictly increasing old-subtype map, a request-tag map preserving
and reflecting the complete request comparison, a request-tag
injection, and ordinal maps preserving natural ordinal values.

This is the generic order criterion. Transport of complete request
comparisons under the genuinely partial target-request constructor
is a separate next step, not silently assumed.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Exact preservation and reflection of the literal old/request/ordinal
comparison by a simultaneous selected-batch map whose old component
has only the selected subtype as its domain. -/
theorem selectedTargetMapSubtype_taggedLex_iff
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hT : Function.Injective T)
    (hTOrder : ∀ r s : SelectedRequests G Allowed bound D,
      RequestLexLt G Allowed bound r.val s.val ↔
        RequestLexLt H AllowedV boundV (T r) (T s))
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ (r : SelectedRequests G Allowed bound D)
      (i : Fin r.val.code.1.val), (phi r i).val = i.val)
    (x y : SelectedCarrier G Allowed bound S D) :
    TaggedLexLt G Allowed bound
      (selectedSourceMap G Allowed bound S D x)
      (selectedSourceMap G Allowed bound S D y) ↔
    TaggedLexLt H AllowedV boundV
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi x)
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi y) := by
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          change u.val < v.val ↔ e u < e v
          constructor
          · intro huv
            exact he huv
          · intro hlt
            rcases lt_trichotomy u v with huv | heq | hvu
            · exact huv
            · cases heq
              exact False.elim (lt_irrefl _ hlt)
            · exact False.elim (lt_asymm (he hvu) hlt)
      | inr z =>
          exact Iff.rfl
  | inr z =>
      cases y with
      | inl v =>
          exact Iff.rfl
      | inr w =>
          rcases z with ⟨r, i⟩
          rcases w with ⟨s, j⟩
          change
            (RequestLexLt G Allowed bound r.val s.val ∨
              (r.val = s.val ∧ i.val < j.val)) ↔
            (RequestLexLt H AllowedV boundV (T r) (T s) ∨
              (T r = T s ∧ (phi r i).val < (phi s j).val))
          have hTag : (r.val = s.val) ↔ T r = T s := by
            constructor
            · intro h
              have hrs : r = s := Subtype.ext h
              rw [hrs]
            · intro h
              exact congrArg Subtype.val (hT h)
          have hOrdinal : i.val < j.val ↔
              (phi r i).val < (phi s j).val := by
            rw [hphi r i, hphi s j]
          exact or_congr (hTOrder r s) (and_congr hTag hOrdinal)

end CFStageCatalogue
end BigHrushovski
