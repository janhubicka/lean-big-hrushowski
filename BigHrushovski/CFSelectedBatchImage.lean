import BigHrushovski.CFActualRequestOrderTransport
import BigHrushovski.CFSelectedClosedSubbatch

/-!
# Strict closure of the image of a simultaneous selected C_F batch

The old source S has already been embedded as a strictly d-closed
finite subset a of the target old stage. At the prescribed next
level, choose any finite family D of actual target requests whose
literal supports lie in a. Attach all blocks of D simultaneously.

The resulting subset of the complete tagged next level is strictly
d-closed in that entire finite level, not merely inside the partial
union. The proof uses the verified supported-subbatch lemma, which
itself handles all requests in D simultaneously.

No induced map of a source batch or order preservation is claimed
in this module. Those are separate parts of finite level lifting.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The old image together with *all* fresh blocks of a selected
family of request tags, as a literal subset of the entire new level. -/
noncomputable def selectedBatchImage
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (a : Finset U)
    (D : Finset (Requests G Allowed bound)) :
    Finset (LevelCarrier G Allowed bound) :=
  a.image Sum.inl ∪ D.biUnion (taggedBlock G Allowed bound)

/-- A strictly d-closed old source and a simultaneous family of
new blocks with supports inside it form a strictly d-closed
subset of the *whole* next tagged level. No choice of a
sequential order on D is made. -/
theorem selectedBatchImage_dClosed_full
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (a : Finset U)
    (hOld : G.toPredimension.IsDClosed a Finset.univ)
    (D : Finset (Requests G Allowed bound))
    (hSupports : ∀ r ∈ D, r.support ⊆ a) :
    (levelGraph G Allowed bound).toPredimension.IsDClosed
      (selectedBatchImage G Allowed bound a D)
      Finset.univ := by
  classical
  have hOldTagged :
      (levelGraph G Allowed bound).toPredimension.IsDClosed
        (a.image Sum.inl)
        (taggedOldDomain G Allowed bound) := by
    simpa only [taggedOldDomain] using
      (G.dClosed_image_iff (levelGraph G Allowed bound)
        Sum.inl Sum.inl_injective
        (fun u v => (levelGraph_old_iff G Allowed bound u v).symm)
        a Finset.univ (Finset.subset_univ _)).mpr hOld
  have hSelected : ∀ r ∈ D,
      taggedSupport G Allowed bound r ⊆ a.image Sum.inl := by
    intro r hr z hz
    obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨u, hSupports r hr hu, huz⟩
  exact taggedSupportClosedSubbatch_dClosed_full
    G Allowed bound D (a.image Sum.inl) hOldTagged hSelected

end CFStageCatalogue
end BigHrushovski
