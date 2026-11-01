import BigHrushovski.CFSelectedCutEquiv
import BigHrushovski.CFActualSubtypeBatchInduced

/-!
# The actual C_F one-step embedding of a literal finite stage cut

The selected carrier is canonically identified with the entire
next-stage cut of a finite b-closed birth-labelled source. Applying
the partial-source simultaneous map through this identification gives
an induced and strictly increasing map of the genuine source cut,
whose image is strictly d-closed in the whole target successor stage.

Crucially, only the selected old source is embedded; no embedding of
the whole ambient source U_n into the old target U_m is required,
even if m < n or U_m is empty.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The inverse selected-cut equivalence has the exact old/fresh
source vertex as its underlying value in the actual successor
stage, not a renamed representative. -/
theorem selectedCutEquiv_symm_val
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n : ℕ)
    (x : SupportCarrier (stage F K (n + 1)).carrier
      (stageCut F K s (n + 1))) :
    selectedSourceMap (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
      ((selectedCutEquiv F K s hs n).symm x) = x.val := by
  simpa only [selectedCutEquiv_val] using
    congrArg Subtype.val
      ((selectedCutEquiv F K s hs n).apply_symm_apply x)

/-- Graph inducedness for the true finite next-cut source, not
only its auxiliary selected old-plus-fresh carrier. -/
theorem selectedCutOneStepLift_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hOldAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (x y : SupportCarrier (stage F K (n+1)).carrier
      (stageCut F K s (n+1))) :
    (stage F K (n+1)).graph.adj x.val y.val ↔
      (stage F K (m+1)).graph.adj
        (selectedCutOneStepLift F K s hs n m e he h x)
        (selectedCutOneStepLift F K s hs n m e he h y) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  change (stage F K (n+1)).graph.adj x.val y.val ↔
    (stage F K (m+1)).graph.adj
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h
        ((selectedCutEquiv F K s hs n).symm x))
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h
        ((selectedCutEquiv F K s hs n).symm y))
  rw [← selectedCutEquiv_symm_val F K s hs n x,
      ← selectedCutEquiv_symm_val F K s hs n y]
  exact selectedGrowthBatchMapSubtype_induced F K
    (stage F K n).graph (stage F K m).graph
    (stageCut F K s n) e he hOldAdj (selectedRequests F K s n)
    h ((selectedCutEquiv F K s hs n).symm x)
      ((selectedCutEquiv F K s hs n).symm y)

/-- The one-step map preserves and reflects the *actual inherited*
stage order on the selected successor cut, not just an arbitrary
order on the auxiliary old/fresh sum. -/
theorem selectedCutOneStepLift_stageOrder_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (x y : SupportCarrier (stage F K (n+1)).carrier
      (stageCut F K s (n+1))) :
    stageLt F K (n+1) x.val y.val ↔
      stageLt F K (m+1)
        (selectedCutOneStepLift F K s hs n m e he h x)
        (selectedCutOneStepLift F K s hs n m e he h y) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  change stageLt F K (n+1) x.val y.val ↔
    stageLt F K (m+1)
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h
        ((selectedCutEquiv F K s hs n).symm x))
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h
        ((selectedCutEquiv F K s hs n).symm y))
  rw [← selectedCutEquiv_symm_val F K s hs n x,
      ← selectedCutEquiv_symm_val F K s hs n y]
  exact selectedGrowthBatchMapSubtype_stageOrder_iff F K n m
    (stageCut F K s n) e he (selectedRequests F K s n) h
    ((selectedCutEquiv F K s hs n).symm x)
    ((selectedCutEquiv F K s hs n).symm y)

/-- The finite image of the literal next-cut map is exactly the
finite image of its simultaneous selected-batch presentation. -/
theorem selectedCutOneStepLift_image_eq
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n)) :
    ((Finset.univ : Finset (SupportCarrier (stage F K (n+1)).carrier
        (stageCut F K s (n+1)))).image
      (selectedCutOneStepLift F K s hs n m e he h)) =
    ((Finset.univ : Finset (CutSelectedCarrier F K s n)).image
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h)) := by
  classical
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  ext v
  constructor
  · intro hv
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    exact ⟨(selectedCutEquiv F K s hs n).symm x,
      Finset.mem_univ _, hx⟩
  · intro hv
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨selectedCutEquiv F K s hs n x,
      Finset.mem_univ _, ?_⟩
    change selectedGrowthBatchMapSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e he (selectedRequests F K s n) h
      ((selectedCutEquiv F K s hs n).symm
        (selectedCutEquiv F K s hs n x)) = v
    rw [Equiv.symm_apply_apply]
    exact hx

/-- The image of the literal next-cut embedding is strictly
d-closed in the *whole* target next stage, not just in a
partial tagged union. -/
theorem selectedCutOneStepLift_dClosed_full
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s) (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) → (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (hOldClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    (stage F K (m+1)).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset
        (SupportCarrier (stage F K (n+1)).carrier
          (stageCut F K s (n+1)))).image
        (selectedCutOneStepLift F K s hs n m e he h))
      Finset.univ := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  rw [selectedCutOneStepLift_image_eq F K s hs n m e he h]
  exact selectedGrowthBatchMapSubtype_dClosed_full F K
    (stage F K n).graph (stage F K m).graph
    (stageCut F K s n) e he (selectedRequests F K s n)
    h hOldClosed

end CFCoherentTower
end BigHrushovski
