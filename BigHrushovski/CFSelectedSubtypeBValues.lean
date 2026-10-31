import BigHrushovski.CFSelectedBatchBValues
import BigHrushovski.CFActualSubtypeSelectedBatch

/-!
# Complete b-values under genuinely partial old-source C_F maps

The selected old embedding e:S→V may have an empty codomain while
the complete old source stage U is nonempty. It must not be extended
to a total map U→V.

A fresh vertex in a selected block has the complete auxiliary
b-value consisting of its entire literal old support and every
vertex of its fresh block. We prove that its image under the
partial-old-source simultaneous map is exactly the corresponding
target support-plus-block value, assuming the target support is
the literal image under e and the ordinal map is surjective.

The actual target request construction gives this support equality
and the canonical finite-ordinal order isomorphism is surjective,
so the complete b-value equality follows without an additional
hypothesis for new vertices.

Older vertices and induction over represented source levels remain
separate.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- Complete b-value transport under a simultaneous selected map
whose old component is defined only on its selected subtype.
The value includes the whole support and the whole fresh block. -/
theorem selectedBlockBValue_image_subtype
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (e : SupportCarrier U S → V)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (r : SelectedRequests G Allowed bound D)
    (hSub : r.val.support ⊆ S)
    (hSupport : (T r).support =
      CFNamedSupport.supportImage S r.val.support hSub e)
    (hphi : Function.Surjective (phi r)) :
    (selectedBlockBValue G Allowed bound S D r hSub).image
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi) =
      taggedSupport H AllowedV boundV (T r) ∪
        taggedBlock H AllowedV boundV (T r) := by
  classical
  unfold selectedBlockBValue
  simp only [Finset.image_union]
  apply congrArg₂ (· ∪ ·)
  · ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
      obtain ⟨p, _, hpw⟩ := Finset.mem_image.mp hw
      subst w
      apply Finset.mem_image.mpr
      refine ⟨e (⟨p.val, hSub p.property⟩ :
          SupportCarrier U S), ?_, ?_⟩
      · rw [hSupport]
        exact Finset.mem_image.mpr
          ⟨p, Finset.mem_attach _ _, rfl⟩
      · exact hwz
    · intro hz
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
      rw [hSupport] at hv
      obtain ⟨p, _, hpv⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨(Sum.inl ⟨p.val, hSub p.property⟩ :
        SelectedCarrier G Allowed bound S D), ?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨p, Finset.mem_attach _ _, rfl⟩
      · change (Sum.inl
          (e ⟨p.val, hSub p.property⟩) :
            LevelCarrier H AllowedV boundV) = z
        exact (congrArg Sum.inl hpv).trans hvz
  · ext z
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
      obtain ⟨i, _, hiw⟩ := Finset.mem_image.mp hw
      subst w
      apply Finset.mem_image.mpr
      exact ⟨phi r i, Finset.mem_univ _, hwz⟩
    · intro hz
      obtain ⟨j, _, hjz⟩ := Finset.mem_image.mp hz
      obtain ⟨i, hij⟩ := hphi j
      apply Finset.mem_image.mpr
      refine ⟨(Sum.inr ⟨r, i⟩ :
        SelectedCarrier G Allowed bound S D), ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, rfl⟩
      · change (Sum.inr ⟨T r, phi r i⟩ :
          LevelCarrier H AllowedV boundV) = z
        rw [hij]
        exact hjz

variable [LinearOrder U] [LinearOrder V]

/-- The actual partial-old-source C_F request transport preserves
the complete b-value of every selected NEW block. Literal support
equality and surjectivity of fresh ordinal maps are supplied by
the constructed request and its canonical Fin order isomorphism. -/
theorem selectedGrowthBatchMapSubtype_bValue_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    (selectedBlockBValue G (GrowthAllowedLocal F)
      (fun P => K P.card) S D r
      (h.supports r.val r.property)).image
        (selectedGrowthBatchMapSubtype F K G H S e he D h) =
      taggedSupport H (GrowthAllowedLocal F) (fun Q => K Q.card)
        (selectedGrowthTagSubtype F K G H S e he D h r) ∪
      taggedBlock H (GrowthAllowedLocal F) (fun Q => K Q.card)
        (selectedGrowthTagSubtype F K G H S e he D h r) := by
  exact selectedBlockBValue_image_subtype
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e
    (selectedGrowthTagSubtype F K G H S e he D h)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)
    r (h.supports r.val r.property)
    (selectedGrowthTagSubtype_support F K G H S e he D h r)
    (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r).surjective

end CFStageCatalogue
end BigHrushovski
