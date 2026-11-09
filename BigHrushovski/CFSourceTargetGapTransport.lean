import BigHrushovski.CFStageCutGapBValues
import BigHrushovski.CFStageAscentDClosed
import BigHrushovski.CFStageBValueAscent

/-!
# The full induction invariant across source and target level gaps

Suppose a finite b-closed source meets no birth level between n and m.
Its literal selected source cut at stage m is canonically equivalent
to its selected source cut at stage n, using exact birth labels.

An old map of the stage-n cut into a target stage U_p can be
transported to the stage-m cut and then advanced by k target
stages to U_(p+k). No map of the entire ambient source stage
is constructed.

The transported map retains:
* complete induced adjacency and nonadjacency;
* the actual inherited stage order;
* strictly d-closed image in the entire later target stage;
* equality of the ENTIRE finite preimage of each actual birth
  b-value with the corresponding target old-stage value.

This is the skipped-level/gap step in the finite-level lifting
induction. It does not assert unique lifting of an arbitrary
finite functional structure or require an increasing self-map
of all natural-number birth levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Relabel an old selected source cut across a gap by literal
birth labels and advance its target images by canonical ascent. -/
noncomputable def sourceTargetGapMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier) :
    SupportCarrier (stage F K m).carrier (stageCut F K s m) →
      (stage F K (p+k)).carrier :=
  fun x => ascend F K p k
    (e ((stageCutGapEquiv F K s n m hnm hGap).symm x))

/-- The gap map is induced including all nonedges, provided
the old selected-domain map is induced. -/
theorem sourceTargetGapMap_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K p).graph.adj (e u) (e v))
    (x y : SupportCarrier (stage F K m).carrier
      (stageCut F K s m)) :
    (stage F K m).graph.adj x.val y.val ↔
      (stage F K (p+k)).graph.adj
        (sourceTargetGapMap F K s n m hnm hGap p k e x)
        (sourceTargetGapMap F K s n m hnm hGap p k e y) := by
  let E := stageCutGapEquiv F K s n m hnm hGap
  have hSource :
      (stage F K m).graph.adj x.val y.val ↔
      (stage F K n).graph.adj (E.symm x).val (E.symm y).val := by
    have h := stageCutGapEquiv_induced F K s n m hnm hGap
      (E.symm x) (E.symm y)
    simpa only [E, Equiv.apply_symm_apply] using h.symm
  exact hSource.trans
    ((hAdj (E.symm x) (E.symm y)).trans
      (ascend_induced F K p k (e (E.symm x)) (e (E.symm y))).symm)

/-- The gap map preserves the exact inherited stage order,
not an arbitrary order on copies of the finite source. -/
theorem sourceTargetGapMap_strictMono
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K p).carrier :=
        stageLinearOrder F K p
      StrictMono e) :
    letI : LinearOrder (stage F K m).carrier :=
      stageLinearOrder F K m
    letI : LinearOrder (stage F K (p+k)).carrier :=
      stageLinearOrder F K (p+k)
    StrictMono (sourceTargetGapMap F K s n m hnm hGap p k e) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  letI : LinearOrder (stage F K p).carrier := stageLinearOrder F K p
  letI : LinearOrder (stage F K (p+k)).carrier :=
    stageLinearOrder F K (p+k)
  let E := stageCutGapEquiv F K s n m hnm hGap
  intro x y hxy
  have hSource :
      stageLt F K n (E.symm x).val (E.symm y).val := by
    have h := stageCutGapEquiv_stageOrder_iff F K s n m
      hnm hGap (E.symm x) (E.symm y)
    apply h.mpr
    change stageLt F K m x.val y.val at hxy
    simpa only [E, Equiv.apply_symm_apply] using hxy
  have hTarget : stageLt F K p
      (e (E.symm x)) (e (E.symm y)) := he hSource
  exact (stageLt_ascend_iff F K p k
    (e (E.symm x)) (e (E.symm y))).mpr hTarget

/-- The exact selected image of the gap map is the image
of the old selected source under the canonical target ascent.
This is an equality of finite sets in the full target stage. -/
theorem sourceTargetGapMap_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier) :
    selectedOldImage (stageCut F K s m)
      (sourceTargetGapMap F K s n m hnm hGap p k e) =
    selectedOldImage (stageCut F K s n)
      (fun u => ascend F K p k (e u)) := by
  classical
  let E := stageCutGapEquiv F K s n m hnm hGap
  ext v
  constructor
  · intro hv
    obtain ⟨x, _, hxv⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨E.symm x, Finset.mem_univ _, hxv⟩
  · intro hv
    obtain ⟨u, _, huv⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨E u, Finset.mem_univ _, ?_⟩
    change ascend F K p k (e (E.symm (E u))) = v
    simpa only [Equiv.symm_apply_apply] using huv

/-- Strict d-closedness of the old selected image persists
in the ENTIRE later target stage, even across arbitrary gaps. -/
theorem sourceTargetGapMap_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (hClosed : (stage F K p).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    (stage F K (p+k)).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s m)
        (sourceTargetGapMap F K s n m hnm hGap p k e))
      Finset.univ := by
  rw [sourceTargetGapMap_image]
  exact selectedOldImage_ascend_dClosed F K p k
    (stageCut F K s n) e hClosed

/-- Complete old birth-b-values persist across BOTH a skipped
source interval and an arbitrary target-stage ascent. The
premise is the exact old-value preservation invariant. -/
theorem sourceTargetGapMap_completeBirthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (hOldB : ∀ u : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image e =
        stageOldBirthBValue F K p (e u))
    (x : SupportCarrier (stage F K m).carrier (stageCut F K s m)) :
    (cutOldBirthBValue F K s m x).image
        (sourceTargetGapMap F K s n m hnm hGap p k e) =
      stageOldBirthBValue F K (p+k)
        (sourceTargetGapMap F K s n m hnm hGap p k e x) := by
  classical
  let E := stageCutGapEquiv F K s n m hnm hGap
  let u := E.symm x
  have hSrc : (cutOldBirthBValue F K s n u).image E =
      cutOldBirthBValue F K s m x := by
    have h := stageCutGapEquiv_completeBirthBValues
      F K s hs n m hnm hGap u
    simpa only [u, E, Equiv.apply_symm_apply] using h
  have hImage :
      ((cutOldBirthBValue F K s n u).image E).image
        (sourceTargetGapMap F K s n m hnm hGap p k e) =
      (cutOldBirthBValue F K s n u).image
        (fun z => ascend F K p k (e z)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
      obtain ⟨a, ha, haw⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨a, ha, ?_⟩
      change ascend F K p k (e a) = v
      calc
        ascend F K p k (e a) =
          ascend F K p k (e (E.symm (E a))) := by
            rw [Equiv.symm_apply_apply]
        _ = ascend F K p k (e (E.symm w)) := by rw [haw]
        _ = v := hwv
    · intro hv
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨E a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
      · change ascend F K p k (e (E.symm (E a))) = v
        simpa only [Equiv.symm_apply_apply] using hav
  have hLater := selectedOldBirthBValues_ascend F K p k
    (stageCut F K s n) e (cutOldBirthBValue F K s n) hOldB u
  calc
    (cutOldBirthBValue F K s m x).image
        (sourceTargetGapMap F K s n m hnm hGap p k e) =
      ((cutOldBirthBValue F K s n u).image E).image
        (sourceTargetGapMap F K s n m hnm hGap p k e) := by
          rw [hSrc]
    _ = (cutOldBirthBValue F K s n u).image
        (fun z => ascend F K p k (e z)) := hImage
    _ = stageOldBirthBValue F K (p+k)
        (ascend F K p k (e u)) := hLater
    _ = stageOldBirthBValue F K (p+k)
        (sourceTargetGapMap F K s n m hnm hGap p k e x) := by
          rfl

end CFCoherentTower
end BigHrushovski
