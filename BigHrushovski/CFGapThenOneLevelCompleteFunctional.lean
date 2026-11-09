import BigHrushovski.CFGapThenOneLevelLift
import BigHrushovski.CFActualCutCompleteFunctionalLift

/-!
# Complete C_F functional lifting after arbitrary source and target gaps

This combines the independently verified exact old-b-value transport
through unrepresented source levels and canonical target-stage ascent
with the automatic one-level lift on the actual selected source cut.

The induction invariant is equality of the COMPLETE actual old
birth-b-value, not merely inclusion of supports. No global self-map
of birth levels, total old ambient-stage map, or unproved uniqueness
principle is used.

The result is a single represented-level induction step. It does not
assert the whole finite multi-level lifting theorem or the uniqueness
of arbitrary functional embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A source-level gap followed by an actual selected successor
preserves all five structural/functional requirements. The only
additional hypothesis beyond structural old-stage embedding is the
complete old birth-b-value induction invariant. -/
theorem gapThenOneLevelMap_completeFunctional
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
    (hOldB : ∀ u : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image e =
        stageOldBirthBValue F K p (e u)) :
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
            (stageCut F K s (m+1)))).image T) Finset.univ ∧
      (∀ x : SupportCarrier (stage F K (m+1)).carrier
          (stageCut F K s (m+1)),
        (cutOldBirthBValue F K s (m+1) x).image T =
          stageOldBirthBValue F K (p+k+1) (T x)) := by
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  letI : LinearOrder (stage F K (p+k)).carrier :=
    stageLinearOrder F K (p+k)
  let eGap := sourceTargetGapMap F K s n m hnm hGap p k e
  have hMono : StrictMono eGap :=
    sourceTargetGapMap_strictMono F K s n m hnm hGap p k e he
  have hAdjGap :
      ∀ x y : SupportCarrier (stage F K m).carrier
          (stageCut F K s m),
        (stage F K m).graph.adj x.val y.val ↔
          (stage F K (p+k)).graph.adj (eGap x) (eGap y) := by
    intro x y
    exact sourceTargetGapMap_induced F K s n m hnm hGap
      p k e hAdj x y
  have hClosedGap :
      (stage F K (p+k)).graph.toPredimension.IsDClosed
        (selectedOldImage (stageCut F K s m) eGap)
        Finset.univ :=
    sourceTargetGapMap_dClosed F K s n m hnm hGap p k e hClosed
  have hBirthGap :
      ∀ x : SupportCarrier (stage F K m).carrier
          (stageCut F K s m),
        (cutOldBirthBValue F K s m x).image
            (fun w => toVertex F K (p+k) (eGap w)) =
          birthBValue F K (toVertex F K (p+k) (eGap x)) := by
    intro x
    exact (oldBValue_image_iff_birthBValue F K s hs m (p+k)
      eGap x).mp
        (sourceTargetGapMap_completeBirthBValues
          F K s hs n m hnm hGap p k e hOldB x)
  exact actualCutLift_completeFunctional F K s hs m (p+k)
    eGap hMono hAdjGap hClosedGap hBirthGap

/-- The composite map transports the literal complete countable
birth-b-value of each selected vertex, old or fresh, onto the
target birth-b-value. This is the form needed at the next
represented-level induction step. -/
theorem gapThenOneLevelMap_completeBirthImage
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
    (hOldB : ∀ u : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image e =
        stageOldBirthBValue F K p (e u))
    (x : SupportCarrier (stage F K (m+1)).carrier
      (stageCut F K s (m+1))) :
    (cutOldBirthBValue F K s (m+1) x).image
      (fun w => toVertex F K (p+k+1)
        (gapThenOneLevelMap F K s hs n m hnm hGap p k
          e he hAdj hClosed w)) =
    birthBValue F K (toVertex F K (p+k+1)
      (gapThenOneLevelMap F K s hs n m hnm hGap p k
        e he hAdj hClosed x)) := by
  let T := gapThenOneLevelMap F K s hs n m hnm hGap
    p k e he hAdj hClosed
  have hValues :
      (cutOldBirthBValue F K s (m+1) x).image T =
        stageOldBirthBValue F K (p+k+1) (T x) :=
    (gapThenOneLevelMap_completeFunctional F K s hs
      n m hnm hGap p k e he hAdj hClosed hOldB).2.2.2.2 x
  calc
    (cutOldBirthBValue F K s (m+1) x).image
        (fun w => toVertex F K (p+k+1) (T w)) =
      ((cutOldBirthBValue F K s (m+1) x).image T).image
        (toVertex F K (p+k+1)) := by
          rw [Finset.image_image]
          rfl
    _ = (stageOldBirthBValue F K (p+k+1) (T x)).image
          (toVertex F K (p+k+1)) := by rw [hValues]
    _ = birthBValue F K (toVertex F K (p+k+1) (T x)) :=
      stageOldBirthBValue_image F K (p+k+1) (T x)

end CFCoherentTower
end BigHrushovski
