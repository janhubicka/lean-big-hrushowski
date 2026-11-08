import BigHrushovski.CFSourceTargetGapTransport
import BigHrushovski.CFActualCutBirthLevelTransport

/-!
# An actual C_F represented-level lifting step after arbitrary gaps

The finite source may skip the interval [n,m), while the prescribed
target may pass from U_p to U_(p+k). An induced strictly increasing
map of the old stage-n selected cut, with strictly d-closed image,
first transports across both gaps. At the next represented source
level m, the automatic one-step construction extends the resulting
genuinely partial map to the actual stage-(m+1) source cut.

The image of this extension is strictly d-closed in the entire
stage U_(p+k+1), not merely in a selected target copy. Old source
birth labels remain the already assigned actual target labels;
new vertices have birth label exactly p+k.

This is ONE induction step, not a global level map, a uniqueness
claim, or a proof of the complete multi-level induction.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The actual one-level successor map after a skipped source
interval and arbitrary target-stage ascent. All maps have genuine
selected source subtypes as their domains. -/
noncomputable def gapThenOneLevelMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K p).carrier :=
        stageLinearOrder F K p
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K p).graph.adj (e u) (e v))
    (hClosed : (stage F K p).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    SupportCarrier (stage F K (m+1)).carrier
      (stageCut F K s (m+1)) →
    (stage F K (p+k+1)).carrier :=
  actualCutLift F K s hs m (p+k)
    (sourceTargetGapMap F K s n m hnm hGap p k e)
    (sourceTargetGapMap_strictMono F K s n m hnm hGap p k e he)
    (sourceTargetGapMap_induced F K s n m hnm hGap p k e hAdj)
    (sourceTargetGapMap_dClosed F K s n m hnm hGap p k e hClosed)

/-- The composite induction step is an induced increasing embedding
with strictly d-closed image in the WHOLE later target stage. -/
theorem gapThenOneLevelMap_structural
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K p).carrier :=
        stageLinearOrder F K p
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K p).graph.adj (e u) (e v))
    (hClosed : (stage F K p).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    let T := gapThenOneLevelMap F K s hs n m hnm hGap p k
      e he hAdj hClosed
    Function.Injective T ∧
      (∀ x y : SupportCarrier (stage F K (m+1)).carrier
          (stageCut F K s (m+1)),
        (stage F K (m+1)).graph.adj x.val y.val ↔
          (stage F K (p+k+1)).graph.adj (T x) (T y)) ∧
      (∀ x y : SupportCarrier (stage F K (m+1)).carrier
          (stageCut F K s (m+1)),
        stageLt F K (m+1) x.val y.val ↔
          stageLt F K (p+k+1) (T x) (T y)) ∧
      (stage F K (p+k+1)).graph.toPredimension.IsDClosed
        ((Finset.univ : Finset
          (SupportCarrier (stage F K (m+1)).carrier
            (stageCut F K s (m+1)))).image T) Finset.univ := by
  exact actualCutLift_oneLevel F K s hs m (p+k)
    (sourceTargetGapMap F K s n m hnm hGap p k e)
    (sourceTargetGapMap_strictMono F K s n m hnm hGap p k e he)
    (sourceTargetGapMap_induced F K s n m hnm hGap p k e hAdj)
    (sourceTargetGapMap_dClosed F K s n m hnm hGap p k e hClosed)

/-- A previously selected source vertex keeps its already assigned
target birth identity after both gaps and the new one-level step. -/
theorem gapThenOneLevelMap_oldBirthExact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K p).carrier :=
        stageLinearOrder F K p
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K p).graph.adj (e u) (e v))
    (hClosed : (stage F K p).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    toVertex F K (p+k+1)
      (gapThenOneLevelMap F K s hs n m hnm hGap p k e he hAdj hClosed
        (selectedCutEquiv F K s hs m
          (Sum.inl (stageCutGapEquiv F K s n m hnm hGap u)))) =
    toVertex F K p (e u) := by
  let E := stageCutGapEquiv F K s n m hnm hGap
  have hOld := actualCutLift_oldBirthExact F K s hs m (p+k)
    (sourceTargetGapMap F K s n m hnm hGap p k e)
    (sourceTargetGapMap_strictMono F K s n m hnm hGap p k e he)
    (sourceTargetGapMap_induced F K s n m hnm hGap p k e hAdj)
    (sourceTargetGapMap_dClosed F K s n m hnm hGap p k e hClosed)
    (E u)
  calc
    toVertex F K (p+k+1)
        (gapThenOneLevelMap F K s hs n m hnm hGap p k e he hAdj hClosed
          (selectedCutEquiv F K s hs m (Sum.inl (E u)))) =
      toVertex F K (p+k)
        (sourceTargetGapMap F K s n m hnm hGap p k e (E u)) := hOld
    _ = toVertex F K p (e u) := by
      change toVertex F K (p+k)
        (ascend F K p k (e (E.symm (E u)))) =
        toVertex F K p (e u)
      rw [Equiv.symm_apply_apply]
      exact toVertex_ascend F K p k (e u)

/-- Every fresh selected source vertex at the next represented
level m is born at EXACT target level p+k in the composite map. -/
theorem gapThenOneLevelMap_freshBirthLevel
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (p k : ℕ)
    (e : SupportCarrier (stage F K n).carrier (stageCut F K s n) →
      (stage F K p).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K p).carrier :=
        stageLinearOrder F K p
      StrictMono e)
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K p).graph.adj (e u) (e v))
    (hClosed : (stage F K p).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (r : SelectedRequests (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s m))
    (i : Fin r.val.code.1.val) :
    (toVertex F K (p+k+1)
      (gapThenOneLevelMap F K s hs n m hnm hGap p k
        e he hAdj hClosed
        (selectedCutEquiv F K s hs m (Sum.inr ⟨r, i⟩)))).1 =
      p+k := by
  exact actualCutLift_freshBirthLevel F K s hs m (p+k)
    (sourceTargetGapMap F K s n m hnm hGap p k e)
    (sourceTargetGapMap_strictMono F K s n m hnm hGap p k e he)
    (sourceTargetGapMap_induced F K s n m hnm hGap p k e hAdj)
    (sourceTargetGapMap_dClosed F K s n m hnm hGap p k e hClosed)
    r i

end CFCoherentTower
end BigHrushovski
