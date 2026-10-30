import BigHrushovski.CFSelectedBatchImageExact
import BigHrushovski.CFPartialOldSourceRequest

/-!
# Simultaneous selected C_F blocks over a genuinely partial old map

The previous tagged-batch map takes a total map from the entire old
stage U to the target old stage V, although only selected old
vertices S⊆U are ever used. Such a total map need not exist if
V=∅ but U is nonempty.

Here the old map has its exact domain {u:U // u∈S}. It sends all
selected source blocks to one target tagged level while keeping
their dependent request tags and fresh ordinal maps. This is
well-typed even for S=∅ and V=∅, so the first represented level
needs no exceptional dummy vertex.

We prove the generic simultaneous map is injective from the old
map, tag-map and ordinal-map injectivity, and identify its exact
image whenever all ordinal maps are surjective. The supported
subbatch theorem then gives strict d-closedness in the ENTIRE
target level under the explicit old-image and support conditions.

The target request map and local inducedness/order/b-value
properties remain separate.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- The literal finite image of the selected old-subtype map. -/
noncomputable def selectedOldImage
    (S : Finset U) (e : SupportCarrier U S → V) : Finset V :=
  (Finset.univ : Finset (SupportCarrier U S)).image e

/-- One simultaneous map of all selected old vertices and all
selected new blocks, with no map defined on U\S. -/
def selectedTargetMapSubtype
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
      Fin r.val.code.1.val → Fin (T r).code.1.val) :
    SelectedCarrier G Allowed bound S D →
      LevelCarrier H AllowedV boundV
  | Sum.inl u => Sum.inl (e u)
  | Sum.inr ⟨r, i⟩ => Sum.inr ⟨T r, phi r i⟩

/-- The simultaneous selected map is injective when the old
partial map, literal request-tag map and within-block ordinal
maps are injective. No extension of e to U→V is required. -/
theorem selectedTargetMapSubtype_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (e : SupportCarrier U S → V)
    (he : Function.Injective e)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hT : Function.Injective T)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ r, Function.Injective (phi r)) :
    Function.Injective
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi) := by
  intro x y h
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          apply congrArg Sum.inl
          exact he (Sum.inl.inj h)
      | inr v => cases h
  | inr x =>
      cases y with
      | inl v => cases h
      | inr y =>
          rcases x with ⟨r, i⟩
          rcases y with ⟨s, j⟩
          have hSigma :
              (⟨T r, phi r i⟩ : FreshCarrier H AllowedV boundV) =
                ⟨T s, phi s j⟩ := Sum.inr.inj h
          have hrs : r = s := hT (congrArg Sigma.fst hSigma)
          cases hrs
          have hij : i = j := by
            apply hphi r
            apply Fin.ext
            exact congrArg
              (fun z : FreshCarrier H AllowedV boundV => z.2.val)
              hSigma
          cases hij
          rfl

/-- The partial simultaneous map has image exactly the old
subtype image and the complete blocks of all selected target
request tags, provided each ordinal map is onto. -/
theorem selectedTargetMapSubtype_image
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
    (hphi : ∀ r, Function.Surjective (phi r)) :
    ((Finset.univ : Finset (SelectedCarrier G Allowed bound S D)).image
      (selectedTargetMapSubtype G Allowed bound
        H AllowedV boundV S D e T phi)) =
      selectedBatchImage H AllowedV boundV
        (selectedOldImage S e)
        (selectedTargetTags G Allowed bound H AllowedV boundV D T) := by
  classical
  letI : Fintype (Requests G Allowed bound) := Fintype.ofFinite _
  unfold selectedBatchImage selectedTargetTags
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    cases x with
    | inl u =>
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_image.mpr
          ⟨e u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, hx⟩
    | inr x =>
        rcases x with ⟨r, i⟩
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_biUnion.mpr
        refine ⟨T r, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨r, by simp, rfl⟩
        · exact Finset.mem_image.mpr
            ⟨phi r i, Finset.mem_univ _, hx⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hOld | hFresh
    · obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hOld
      obtain ⟨u, _, huv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨Sum.inl u, Finset.mem_univ _, by
          change (Sum.inl (e u) : LevelCarrier H AllowedV boundV) = z
          exact (congrArg Sum.inl huv).trans hvz⟩
    · obtain ⟨t, ht, htz⟩ := Finset.mem_biUnion.mp hFresh
      obtain ⟨r, _, hrt⟩ := Finset.mem_image.mp ht
      subst t
      obtain ⟨j, _, hjz⟩ := Finset.mem_image.mp htz
      obtain ⟨i, hi⟩ := hphi r j
      exact Finset.mem_image.mpr
        ⟨Sum.inr ⟨r, i⟩, Finset.mem_univ _, by
          change (Sum.inr ⟨T r, phi r i⟩ :
            LevelCarrier H AllowedV boundV) = z
          rw [hi]
          exact hjz⟩

/-- If the partial old image is d-closed in the old target stage
and all target request supports lie in it, the ENTIRE image of
the simultaneous selected map is d-closed in the complete target
tagged level. No sequential block attachment is used. -/
theorem selectedTargetMapSubtype_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (e : SupportCarrier U S → V)
    (hOld : H.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hSupports : ∀ r, (T r).support ⊆ selectedOldImage S e)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ r, Function.Surjective (phi r)) :
    (levelGraph H AllowedV boundV).toPredimension.IsDClosed
      ((Finset.univ : Finset (SelectedCarrier G Allowed bound S D)).image
        (selectedTargetMapSubtype G Allowed bound
          H AllowedV boundV S D e T phi))
      Finset.univ := by
  classical
  rw [selectedTargetMapSubtype_image G Allowed bound
    H AllowedV boundV S D e T phi hphi]
  apply selectedBatchImage_dClosed_full H AllowedV boundV
    (selectedOldImage S e) hOld
    (selectedTargetTags G Allowed bound H AllowedV boundV D T)
  intro t ht
  change t ∈ D.attach.image T at ht
  obtain ⟨r, _, hrt⟩ := Finset.mem_image.mp ht
  subst t
  exact hSupports r

end CFStageCatalogue
end BigHrushovski
