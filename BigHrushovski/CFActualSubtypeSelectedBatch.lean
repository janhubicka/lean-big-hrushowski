import BigHrushovski.CFSelectedBatchSubtypeMap
import BigHrushovski.CFPartialOldSourceCode

/-!
# Actual simultaneous C_F transport over a genuinely partial old source

Finite unique level lifting begins with a map defined only on the
selected old source S. At the first represented level S and its target
old stage may both be empty, even when the complete source old stage
is nonempty. There is then no total map from the source stage into the
target stage.

This module constructs all target request tags over the literal images
of supports under the actual subtype map e : S → V. The fresh ordinal
intervals are matched by their canonical order isomorphisms, and all
selected blocks are sent to a single target level simultaneously.

We identify the complete image and prove it is strictly d-closed in the
whole target tagged level, provided the selected old image is strictly
d-closed. The actual target-tag map's injectivity, inducedness and
the precise stage order require further verification; no artificial
extension of e outside S is introduced here.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Local conditions on a finite family of requests to transport them
over an old map whose domain is exactly the selected source subtype.
They include the induced old graph and d-closedness of each literal
target support, but do not assume an embedding of the full old stage. -/
structure SelectedGrowthTransportSubtype
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card))) : Prop where
  supports : ∀ r ∈ D, r.support ⊆ S
  induced : ∀ r ∈ D, ∀ hSub : r.support ⊆ S,
    ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩)
  closed : ∀ r ∈ D, ∀ hSub : r.support ⊆ S,
    H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ

/-- The literal target request for each selected source request,
built using only the prescribed old-subtype map e. -/
noncomputable def selectedGrowthTagSubtype
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D) :
    SelectedRequests G (GrowthAllowedLocal F) (fun P => K P.card) D →
      Requests H (GrowthAllowedLocal F) (fun Q => K Q.card) :=
  fun r => transportGrowthStageRequest_partial F K G H S e he r.val
    (h.supports r.val r.property)
    (h.induced r.val r.property (h.supports r.val r.property))
    (h.closed r.val r.property (h.supports r.val r.property))

/-- The actual new request has exactly the literal image of the old
support under the prescribed subtype map. -/
theorem selectedGrowthTagSubtype_support
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    (selectedGrowthTagSubtype F K G H S e he D h r).support =
      CFNamedSupport.supportImage S r.val.support
        (h.supports r.val r.property) e := by
  exact transportGrowthStageRequest_partial_support F K G H S e he
    r.val (h.supports r.val r.property)
    (h.induced r.val r.property (h.supports r.val r.property))
    (h.closed r.val r.property (h.supports r.val r.property))

/-- The canonical increasing identification of the source fresh
interval with that of its actual transported target request. -/
noncomputable def selectedGrowthOrdinalIsoSubtype
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    Fin r.val.code.1.val ≃o
      Fin (selectedGrowthTagSubtype F K G H S e he D h r).code.1.val :=
  Fin.castOrderIso
    (transportGrowthStageRequest_partial_size F K G H S e he
      r.val (h.supports r.val r.property)
      (h.induced r.val r.property (h.supports r.val r.property))
      (h.closed r.val r.property (h.supports r.val r.property))).symm

/-- The ordinal identification is literal: no position inside a
fresh block is changed by relabelling its old support. -/
theorem selectedGrowthOrdinalIsoSubtype_val
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (i : Fin r.val.code.1.val) :
    (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i).val =
      i.val := by
  simp [selectedGrowthOrdinalIsoSubtype]

/-- The actual simultaneous map of the selected old subtype and all
its fresh blocks, with no map from the entire old carrier U to V. -/
noncomputable def selectedGrowthBatchMapSubtype
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D) :
    SelectedCarrier G (GrowthAllowedLocal F) (fun P => K P.card) S D →
      LevelCarrier H (GrowthAllowedLocal F) (fun Q => K Q.card) :=
  selectedTargetMapSubtype
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e (selectedGrowthTagSubtype F K G H S e he D h)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)

/-- Every transported literal support lies in the full image of the
selected old subtype; this uses no values of e outside that subtype. -/
theorem selectedGrowthTagSubtype_support_subset_oldImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    (selectedGrowthTagSubtype F K G H S e he D h r).support ⊆
      selectedOldImage S e := by
  rw [selectedGrowthTagSubtype_support]
  intro v hv
  obtain ⟨p, _, hpv⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr
    ⟨(⟨p.val, (h.supports r.val r.property) p.property⟩ :
       SupportCarrier U S), Finset.mem_univ _, hpv⟩

/-- The actual simultaneous map's complete image is strictly
d-closed in the ENTIRE target tagged level, including when its
old target carrier is empty. This is conditional only on
d-closedness of the prescribed old image; the selected
new supports lie in it by construction. -/
theorem selectedGrowthBatchMapSubtype_dClosed_full
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (hOld : H.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ) :
    (levelGraph H (GrowthAllowedLocal F)
      (fun Q => K Q.card)).toPredimension.IsDClosed
      ((Finset.univ : Finset (SelectedCarrier G
        (GrowthAllowedLocal F) (fun P => K P.card) S D)).image
        (selectedGrowthBatchMapSubtype F K G H S e he D h))
      Finset.univ := by
  exact selectedTargetMapSubtype_dClosed_full
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e hOld
    (selectedGrowthTagSubtype F K G H S e he D h)
    (selectedGrowthTagSubtype_support_subset_oldImage
      F K G H S e he D h)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)
    (fun r =>
      (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r).surjective)

end CFStageCatalogue
end BigHrushovski
