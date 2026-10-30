import BigHrushovski.CFSelectedBatchImageExact
import BigHrushovski.CFActualSelectedBatchMap

/-!
# Complete b-values of the selected C_F blocks in one level

A new vertex in a tagged C_F block has the complete unary value
b(v) = P_r ∪ B_r, where P_r is its literal old support and B_r its
entire request-tagged block.

The actual simultaneous map has a selected old source and all
selected fresh blocks. We define the *complete* source b-value
inside this selected carrier, including all old support vertices,
and prove it maps ONTO the complete target b-value. This requires
literal support-image equality and surjectivity of the fresh
ordinal map, not merely an induced graph embedding.

The proof is independent of the growth function, and so can be
reused in any other tagged finite construction. Applying it to
the actual C_F target request and canonical ordinal isomorphism
is the next direct corollary.

This deals with values for new blocks at one represented level.
The b-values of old vertices must be preserved by the induction
hypothesis; the full finite unique level-lifting theorem is not
claimed here.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [DecidableEq U]
variable [Fintype V] [DecidableEq V]

/-- The complete auxiliary b-value of a selected fresh vertex,
expressed inside the selected old-plus-fresh carrier. It consists
of the full named old support and EVERY ordinal of its block. -/
noncomputable def selectedBlockBValue
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (r : SelectedRequests G Allowed bound D)
    (hSub : r.val.support ⊆ S) :
    Finset (SelectedCarrier G Allowed bound S D) := by
  classical
  let olds : Finset (SelectedCarrier G Allowed bound S D) :=
    r.val.support.attach.image (fun p =>
      (Sum.inl (⟨p.val, hSub p.property⟩ : SupportCarrier U S) :
        SelectedCarrier G Allowed bound S D))
  let fresh : Finset (SelectedCarrier G Allowed bound S D) :=
    (Finset.univ : Finset (Fin r.val.code.1.val)).image
      (fun i => (Sum.inr ⟨r, i⟩ :
        SelectedCarrier G Allowed bound S D))
  exact olds ∪ fresh

/-- Under an actual simultaneous tagged map, the complete
selected b-value maps to the literal target support together
with the entire target block. The support equality and
surjectivity of the fresh ordinal map are essential. -/
theorem selectedBlockBValue_image
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
      Fin r.val.code.1.val → Fin (T r).code.1.val)
    (r : SelectedRequests G Allowed bound D)
    (hSub : r.val.support ⊆ S)
    (hSupport : (T r).support = r.val.support.image f)
    (hphi : Function.Surjective (phi r)) :
    (selectedBlockBValue G Allowed bound S D r hSub).image
      (selectedTargetMap G Allowed bound H AllowedV boundV
        S D f T phi) =
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
      refine ⟨f p.val, ?_, ?_⟩
      · rw [hSupport]
        exact Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩
      · exact hwz
    · intro hz
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
      rw [hSupport] at hv
      obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨(Sum.inl ⟨u, hSub hu⟩ :
        SelectedCarrier G Allowed bound S D), ?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨⟨u, hu⟩, Finset.mem_attach _ _, rfl⟩
      · change (Sum.inl (f u) :
          LevelCarrier H AllowedV boundV) = z
        exact (congrArg Sum.inl huv).trans hvz
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

end CFStageCatalogue
end BigHrushovski
