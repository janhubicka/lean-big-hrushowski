import BigHrushovski.CFActualCutBirthBValueSource
import BigHrushovski.CFPartialOneLevelFunctional
import BigHrushovski.CFSelectedCutEquiv
import BigHrushovski.CFActualSubtypeSelectedBatch

/-!
# Complete actual birth-b-values under one partial C_F level lift

The old/new selected-carrier b-value theorem is already verified,
but its auxiliary target value has a separate recursive definition.
We first identify that value with the literal full-stage
preimage of the actual countable birthBValue, for EVERY target
old or fresh vertex.

We then instantiate the all-vertex selected-carrier theorem with
the unique literal old-b-value preimages of the source cut and
target old stage. The old premise is stated equivalently as
preservation of the TRUE complete countable birth-b-value.

Finally we transport the resulting equality through the
canonical selectedCutEquiv to obtain an exact all-vertex
complete-value equation on the ACTUAL finite source next cut.

No total map of the ambient source old stage, no target-level
gap assumption, and no uniqueness for arbitrary embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The auxiliary target one-level value, old or fresh, has the
exact complete countable birth-b-value as its canonical image. -/
theorem targetOneLevelBValue_birthImage
    (F : ℕ → ℝ) (K : ℕ → ℕ) (m : ℕ)
    (x : (stage F K (m + 1)).carrier) :
    (targetOneLevelBValue (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageOldBirthBValue F K m) x).image
        (toVertex F K (m + 1)) =
      birthBValue F K (toVertex F K (m + 1) x) := by
  classical
  cases x with
  | inl u =>
      change
        ((stageOldBirthBValue F K m u).image
          (fun w : (stage F K m).carrier =>
            (Sum.inl w : (stage F K (m + 1)).carrier))).image
              (toVertex F K (m + 1)) =
        birthBValue F K (toVertex F K m u)
      have hOldImage :
          ((stageOldBirthBValue F K m u).image
            (fun w : (stage F K m).carrier =>
              (Sum.inl w : (stage F K (m + 1)).carrier))).image
                (toVertex F K (m + 1)) =
          (stageOldBirthBValue F K m u).image
            (toVertex F K m) := by
        ext v
        constructor
        · intro hv
          obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
          obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
          apply Finset.mem_image.mpr
          refine ⟨a, ha, ?_⟩
          calc
            toVertex F K m a =
                toVertex F K (m + 1) (Sum.inl a) :=
              (toVertex_old F K m a).symm
            _ = toVertex F K (m + 1) w := by rw [haw]
            _ = v := hwv
        · intro hv
          obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
          apply Finset.mem_image.mpr
          refine ⟨Sum.inl a, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
          · calc
              toVertex F K (m + 1) (Sum.inl a) =
                  toVertex F K m a := toVertex_old F K m a
              _ = v := hav
      exact hOldImage.trans (stageOldBirthBValue_image F K m u)
  | inr z =>
      rcases z with ⟨r, i⟩
      change
        (taggedSupport (stage F K m).graph
          (GrowthAllowedLocal F) (fun P => K P.card) r ∪
         taggedBlock (stage F K m).graph
          (GrowthAllowedLocal F) (fun P => K P.card) r).image
          (toVertex F K (m + 1)) =
        birthBValue F K (⟨m, ⟨r, i⟩⟩ : Vertex F K)
      rw [birthBValue_of_fresh]
      exact Finset.image_union

/-- The parametrized target one-level b-value is LITERALLY the
finite-stage preimage of the TRUE complete birth-b-value.
Injectivity of the target stage's canonical birth map is used. -/
theorem targetOneLevelBValue_eq_stageBirth
    (F : ℕ → ℝ) (K : ℕ → ℕ) (m : ℕ)
    (x : (stage F K (m + 1)).carrier) :
    targetOneLevelBValue (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageOldBirthBValue F K m) x =
    stageOldBirthBValue F K (m + 1) x := by
  classical
  apply Finset.image_injective (toVertex_injective F K (m + 1))
  exact (targetOneLevelBValue_birthImage F K m x).trans
    (stageOldBirthBValue_image F K (m + 1) x).symm

/-- The genuinely partial simultaneous selected level map preserves
complete ACTUAL finite-stage b-values on every old or new vertex,
assuming old source vertices already preserve complete
countable birth-b-values under the prescribed old map. -/
theorem selectedBatch_completeActualBirthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (hOldBirth : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K m (e w)) =
      birthBValue F K (toVertex F K m (e u)))
    (x : CutSelectedCarrier F K s n) :
    letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
    (selectedOneLevelBValue (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (stageCut F K s n) (selectedRequests F K s n)
      (fun r => h.supports r.val r.property)
      (cutOldBirthBValue F K s n) x).image
        (selectedGrowthBatchMapSubtype F K
          (stage F K n).graph (stage F K m).graph
          (stageCut F K s n) e he (selectedRequests F K s n) h) =
      stageOldBirthBValue F K (m + 1)
        (selectedGrowthBatchMapSubtype F K
          (stage F K n).graph (stage F K m).graph
          (stageCut F K s n) e he (selectedRequests F K s n) h x) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  have hOldFinite : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image e =
        stageOldBirthBValue F K m (e u) := by
    intro u
    exact (oldBValue_image_iff_birthBValue F K s hs n m e u).mpr
      (hOldBirth u)
  exact (selectedGrowthBatchMapSubtype_allBValues F K
    (stage F K n).graph (stage F K m).graph
    (stageCut F K s n) e he (selectedRequests F K s n) h
    (cutOldBirthBValue F K s n)
    (stageOldBirthBValue F K m) hOldFinite x).trans
    (targetOneLevelBValue_eq_stageBirth F K m
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h x))

/-- The actual one-step partial map, with domain the literal
next cut (rather than an auxiliary selected carrier), sends
EVERY complete source finite birth-b-value onto the exact
complete target finite-stage birth-b-value. The old-value
preservation premise is the precise induction hypothesis. -/
theorem selectedCutOneStepLift_completeActualBirthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n))
    (hOldBirth : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K m (e w)) =
      birthBValue F K (toVertex F K m (e u)))
    (x : SupportCarrier (stage F K (n + 1)).carrier
      (stageCut F K s (n + 1))) :
    letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
    (cutOldBirthBValue F K s (n + 1) x).image
      (selectedCutOneStepLift F K s hs n m e he h) =
    stageOldBirthBValue F K (m + 1)
      (selectedCutOneStepLift F K s hs n m e he h x) := by
  classical
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  let z := (selectedCutEquiv F K s hs n).symm x
  let B := selectedOneLevelBValue (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card)
    (stageCut F K s n) (selectedRequests F K s n)
    (fun r => h.supports r.val r.property)
    (cutOldBirthBValue F K s n) z
  have hSrc : B.image (selectedCutEquiv F K s hs n) =
      cutOldBirthBValue F K s (n + 1) x := by
    have h := selectedCut_oneLevelBValue_eq_actualCut F K s hs n z
    change B.image (selectedCutEquiv F K s hs n) =
      cutOldBirthBValue F K s (n + 1)
        (selectedCutEquiv F K s hs n z) at h
    simpa only [z, Equiv.apply_symm_apply] using h
  have hAll := selectedBatch_completeActualBirthBValues
    F K s hs n m e he h hOldBirth z
  have hPointwise :
      ∀ y : CutSelectedCarrier F K s n,
        selectedCutOneStepLift F K s hs n m e he h
          (selectedCutEquiv F K s hs n y) =
        selectedGrowthBatchMapSubtype F K
          (stage F K n).graph (stage F K m).graph
          (stageCut F K s n) e he (selectedRequests F K s n) h y := by
    intro y
    change selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h
        ((selectedCutEquiv F K s hs n).symm
          (selectedCutEquiv F K s hs n y)) =
      selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h y
    rw [Equiv.symm_apply_apply]
  have hMapImage :
      (B.image (selectedCutEquiv F K s hs n)).image
        (selectedCutOneStepLift F K s hs n m e he h) =
      B.image (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h) := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      apply Finset.mem_image.mpr
      refine ⟨y, hy, ?_⟩
      calc
        selectedGrowthBatchMapSubtype F K
            (stage F K n).graph (stage F K m).graph
            (stageCut F K s n) e he (selectedRequests F K s n) h y =
          selectedCutOneStepLift F K s hs n m e he h
            (selectedCutEquiv F K s hs n y) := (hPointwise y).symm
        _ = selectedCutOneStepLift F K s hs n m e he h x := by rw [hyx]
        _ = v := hxv
    · intro hv
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨selectedCutEquiv F K s hs n y, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
      · exact (hPointwise y).trans hyv
  have hFirst :
      (cutOldBirthBValue F K s (n + 1) x).image
        (selectedCutOneStepLift F K s hs n m e he h) =
      (B.image (selectedCutEquiv F K s hs n)).image
        (selectedCutOneStepLift F K s hs n m e he h) :=
    congrArg
      (fun Q : Finset
        (SupportCarrier (stage F K (n + 1)).carrier
          (stageCut F K s (n + 1))) =>
        Q.image (selectedCutOneStepLift F K s hs n m e he h))
      hSrc.symm
  calc
    (cutOldBirthBValue F K s (n + 1) x).image
        (selectedCutOneStepLift F K s hs n m e he h) =
      (B.image (selectedCutEquiv F K s hs n)).image
        (selectedCutOneStepLift F K s hs n m e he h) := hFirst
    _ = B.image (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph
        (stageCut F K s n) e he (selectedRequests F K s n) h) :=
      hMapImage
    _ = stageOldBirthBValue F K (m + 1)
        (selectedGrowthBatchMapSubtype F K
          (stage F K n).graph (stage F K m).graph
          (stageCut F K s n) e he (selectedRequests F K s n) h z) := hAll
    _ = stageOldBirthBValue F K (m + 1)
        (selectedCutOneStepLift F K s hs n m e he h x) := by
          rfl

end CFCoherentTower
end BigHrushovski
