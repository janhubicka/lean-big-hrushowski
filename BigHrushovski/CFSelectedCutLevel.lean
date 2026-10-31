import BigHrushovski.CFBirthBlockClosure
import BigHrushovski.CFPartialSupportAutomaticClosure
import BigHrushovski.CFSelectedBatchImageExact

/-!
# The literal selected-batch presentation of a finite C_F source cut

The unique level-lifting induction works with the actual finite
b-closed source cut, not an isomorphic copy of a renamed source.

For a finite closed set of birth vertices, its stage-(n+1) cut
is exactly the image of the selected old cut and the complete
blocks of all selected requests born at stage n. Every selected
request support lies in the literal old cut.

The pre-existing closure and request construction theorems then
give a simultaneous target request transport certificate from
one induced, strictly d-closed old-source embedding. We do not
assume a map of the complete source stage to the target stage.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every source request selected by a b-closed finite set has
its literal old support inside the preceding stage cut. -/
theorem selectedRequests_support_subset_stageCut
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) :
    ∀ r ∈ selectedRequests F K s n,
      r.support ⊆ stageCut F K s n := by
  intro r hr u hu
  obtain ⟨i, hi⟩ :=
    (mem_selectedRequests_iff F K s n r).mp hr
  exact (mem_stageCut_iff F K s n u).mpr
    ((hs n r i hi).2 u hu)

/-- The complete next source cut is precisely the literal image of
one selected old-plus-fresh carrier. No vertices or parts of blocks
are omitted, and no artificial enumeration is introduced. -/
theorem stageCut_succ_eq_selectedSourceImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) :
    ((Finset.univ : Finset
      (SelectedCarrier (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        (stageCut F K s n) (selectedRequests F K s n))).image
      (selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        (stageCut F K s n) (selectedRequests F K s n))) =
      stageCut F K s (n + 1) := by
  classical
  calc
    _ = selectedBatchImage (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          (stageCut F K s n) (selectedRequests F K s n) :=
        selectedSourceMap_image (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          (stageCut F K s n) (selectedRequests F K s n)
    _ = stageCut F K s (n + 1) :=
      (stageCut_succ_eq_selected F K s hs n).symm

/-- A single old embedding, induced and strictly d-closed on its
literal selected domain, automatically supplies every local
transport certificate for the complete family of next-cut blocks.
No separate per-request old graph or strict closure premise. -/
theorem selectedCut_growthTransport_of_induced_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : Function.Injective e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hImageClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n) := by
  exact selectedGrowthTransportSubtype_of_induced_dClosed
    F K (stage F K n).graph (stage F K m).graph
    (stageCut F K s n) e he hAdj hImageClosed
    (selectedRequests F K s n)
    (selectedRequests_support_subset_stageCut F K s hs n)

end CFCoherentTower
end BigHrushovski
