import BigHrushovski.CFSelectedBatchMaps

/-!
# Exact image and d-closure of a simultaneous selected C_F block map

The entire selected old source and all selected fresh blocks are mapped
in one step to the target level. Here we prove that, if the finite
ordinal maps are onto, its *exact* image is the old vertex image
together with the complete target blocks indexed by the image of the
selected request-tag family.

Combining this image equation with the already checked supported
subbatch lemma yields strict d-closedness in the whole target level.
This avoids any attempt to iterate one-block extensions, which would
incorrectly place subsequent blocks at later birth levels.

The map is not yet asserted to preserve the actual local graph codes
or the prescribed order. Those are separate, necessary lifting steps.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- The selected request tags in the target level are exactly the
image of the selected source request subtype. -/
noncomputable def selectedTargetTags
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (D : Finset (Requests G Allowed bound))
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV) :
    Finset (Requests H AllowedV boundV) := by
  classical
  exact D.attach.image T

/-- Exact full image of the simultaneous map. Surjectivity
within each fresh ordinal block is essential: a proper increasing
injection would leave part of a target block outside the image. -/
theorem selectedTargetMap_image
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (f : U → V)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.1.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ r, Function.Surjective (phi r)) :
    ((Finset.univ : Finset (SelectedCarrier G Allowed bound S D)).image
      (selectedTargetMap G Allowed bound H AllowedV boundV
        S D f T phi)) =
    selectedBatchImage H AllowedV boundV
      (S.image f)
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
          ⟨f u.val,
            Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩,
            hx⟩
    | inr x =>
        rcases x with ⟨r, i⟩
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_biUnion.mpr
        refine ⟨T r, ?_, ?_⟩
        · exact Finset.mem_image.mpr
            ⟨r, by simp, rfl⟩
        · exact Finset.mem_image.mpr
            ⟨phi r i, Finset.mem_univ _, hx⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hOld | hFresh
    · obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hOld
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr
        ⟨Sum.inl ⟨u, hu⟩, Finset.mem_univ _, by
          change (Sum.inl (f u) : LevelCarrier H AllowedV boundV) = z
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

/-- The selected source-carrier embedding has exactly the union of
the selected old source and *all* its chosen tagged fresh blocks
as its image inside the original complete tagged level. -/
theorem selectedSourceMap_image
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound)) :
    ((Finset.univ : Finset (SelectedCarrier G Allowed bound S D)).image
      (selectedSourceMap G Allowed bound S D)) =
    selectedBatchImage G Allowed bound S D := by
  classical
  have hD :
      D.attach.image (fun r : SelectedRequests G Allowed bound D => r.val) =
        D := by
    ext r
    simp
  have h := selectedTargetMap_image G Allowed bound
    G Allowed bound S D (fun u : U => u)
    (fun r : SelectedRequests G Allowed bound D => r.val)
    (fun r i => i) (fun r j => ⟨j, rfl⟩)
  have hMap :
      selectedTargetMap G Allowed bound G Allowed bound S D
          (fun u : U => u)
          (fun r : SelectedRequests G Allowed bound D => r.val)
          (fun r i => i) =
        selectedSourceMap G Allowed bound S D := by
    funext x
    cases x with
    | inl u => rfl
    | inr x =>
        rcases x with ⟨r, i⟩
        rfl
  rw [← hMap]
  simpa [selectedTargetTags, hD] using h

/-- The complete image of the selected map is strictly d-closed
in the *entire* target level. All new blocks are attached
simultaneously, and nothing is assumed about a sequential
ordering of the selected requests. -/
theorem selectedTargetMap_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (f : U → V)
    (hOld : H.toPredimension.IsDClosed
      (S.image f) Finset.univ)
    (T : SelectedRequests G Allowed bound D →
      Requests H AllowedV boundV)
    (hSupports : ∀ r, (T r).support ⊆ S.image f)
    (phi : ∀ r : SelectedRequests G Allowed bound D,
      Fin r.1.code.1.val → Fin (T r).code.1.val)
    (hphi : ∀ r, Function.Surjective (phi r)) :
    (levelGraph H AllowedV boundV).toPredimension.IsDClosed
      ((Finset.univ : Finset (SelectedCarrier G Allowed bound S D)).image
        (selectedTargetMap G Allowed bound H AllowedV boundV
          S D f T phi))
      Finset.univ := by
  classical
  rw [selectedTargetMap_image G Allowed bound H AllowedV boundV
    S D f T phi hphi]
  apply selectedBatchImage_dClosed_full H AllowedV boundV
    (S.image f) hOld
    (selectedTargetTags G Allowed bound H AllowedV boundV D T)
  intro t ht
  change t ∈ D.attach.image T at ht
  obtain ⟨r, _, hrt⟩ := Finset.mem_image.mp ht
  subst t
  exact hSupports r

end CFStageCatalogue
end BigHrushovski
