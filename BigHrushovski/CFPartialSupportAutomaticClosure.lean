import BigHrushovski.CFActualSubtypeRequestOrder
import BigHrushovski.CFDClosedTransport

/-!
# Automatically obtain the partial C_F local support certificates

For finite lifting, the old map is defined only on a selected finite
subset S of the complete old source U. If that map is induced, its
image is strictly d-closed in the target old stage, and each selected
source request has support inside S, then every target named support
is automatically strictly d-closed.

This follows by restricting the original strict closure of the source
support to S, transporting it through the induced subtype embedding,
then using transitivity. In particular this removes all per-request
inducedness and target-closure assumptions from the one-level
transport construction. No arbitrary map U → V is used.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The old selected subtype has as its literal image exactly S
under the inclusion to the old source stage. -/
theorem selectedSubtype_univ_image_val (S : Finset U) :
    ((Finset.univ : Finset (SupportCarrier U S)).image
      (fun u : SupportCarrier U S => u.val)) = S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, _, hux⟩ := Finset.mem_image.mp hx
    exact hux ▸ u.property
  · intro hx
    exact Finset.mem_image.mpr
      ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

/-- Strict closure of a literal named source support transports
through an induced map of just the selected old subtype, provided
that the image of the selected subtype is strictly d-closed in
the whole target old graph. -/
theorem supportImage_partial_dClosed_of_induced
    (G : GraphOn U) (H : GraphOn V)
    (S P : Finset U) (hPS : P ⊆ S)
    (hPClosed : G.toPredimension.IsDClosed P Finset.univ)
    (e : SupportCarrier U S → V)
    (he : Function.Injective e)
    (hAdj : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (e u) (e v))
    (hImageClosed : H.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ) :
    H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S P hPS e) Finset.univ := by
  classical
  let GS : GraphOn (SupportCarrier U S) := G.pullback Subtype.val
  let Q : Finset (SupportCarrier U S) := supportInside S P hPS
  have hPInS : G.toPredimension.IsDClosed P S := by
    refine ⟨hPS, ?_⟩
    intro X hPX hNe hXS
    exact hPClosed.2 X hPX hNe
      (hXS.trans (Finset.subset_univ S))
  have hSrc : GS.toPredimension.IsDClosed Q Finset.univ := by
    have hTransport :=
      (GS.dClosed_image_iff G
        (fun u : SupportCarrier U S => u.val)
        (by intro a b h; exact Subtype.ext h)
        (by intro a b; rfl)
        Q Finset.univ (Finset.subset_univ Q))
    apply hTransport.mp
    simpa only [Q, supportInside_image_val,
      selectedSubtype_univ_image_val] using hPInS
  have hDst : H.toPredimension.IsDClosed
      (Q.image e)
      ((Finset.univ : Finset (SupportCarrier U S)).image e) := by
    apply (GS.dClosed_image_iff H e he
      (by intro a b; exact hAdj a b)
      Q Finset.univ (Finset.subset_univ Q)).mpr
    exact hSrc
  have hRel : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S P hPS e)
      (selectedOldImage S e) := by
    simpa only [Q, supportInside_image_partial,
      selectedOldImage] using hDst
  exact H.toPredimension.dclosed_trans hRel hImageClosed

/-- All local transport certificates are consequences of a single
old induced embedding with strictly d-closed image, together with
inclusion of each selected request support in the old selected set. -/
theorem selectedGrowthTransportSubtype_of_induced_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : Function.Injective e)
    (hAdj : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (e u) (e v))
    (hImageClosed : H.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (hSupports : ∀ r ∈ D, r.support ⊆ S) :
    SelectedGrowthTransportSubtype F K G H S e D := by
  refine ⟨hSupports, ?_, ?_⟩
  · intro r hr hSub p q
    exact hAdj ⟨p.val, hSub p.property⟩
      ⟨q.val, hSub q.property⟩
  · intro r hr hSub
    exact supportImage_partial_dClosed_of_induced
      G H S r.support hSub r.supportClosed
      e he hAdj hImageClosed

end CFStageCatalogue
end BigHrushovski
