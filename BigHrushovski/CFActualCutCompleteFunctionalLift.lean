import BigHrushovski.CFActualCutAutomaticLift
import BigHrushovski.CFActualCutBValueLift

/-!
# Complete one-level C_F functional lifting on the actual finite source cut

A strictly increasing induced map of the selected old source cut,
with strictly d-closed image in its prescribed target old stage,
automatically determines the simultaneous requested successor map.

If that old map additionally preserves the complete ACTUAL
countable birth-b-values, then the successor map preserves
and reflects graph edges, the actual inherited finite-stage order,
and maps every vertex's complete birth-b-value ONTO its target value.

We package the four structural conclusions and the full
functional-value equality in one statement, with hypotheses
explicitly restricted to the OLD SELECTED SUBTYPE.

This is an induction-facing finite one-level theorem, not a
multi-level finite unique level-lifting theorem, and it does not
prove intrinsic uniqueness among arbitrary functional maps.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- One actual C_F successor level, with no per-request transport
hypotheses: an induced, strictly increasing, d-closed old-source
map preserving all complete true old birth-b-values extends to
an injective, induced, order-preserving, strictly d-closed
successor map preserving all complete birth-b-values. -/
theorem actualCutLift_completeFunctional
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
    (hAdj : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hOldClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage (stageCut F K s n) e) Finset.univ)
    (hOldBirth : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K m (e w)) =
      birthBValue F K (toVertex F K m (e u))) :
    letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
    let T := actualCutLift F K s hs n m e he hAdj hOldClosed
    Function.Injective T ∧
      (∀ x y : SupportCarrier (stage F K (n+1)).carrier
          (stageCut F K s (n+1)),
        (stage F K (n+1)).graph.adj x.val y.val ↔
          (stage F K (m+1)).graph.adj (T x) (T y)) ∧
      (∀ x y : SupportCarrier (stage F K (n+1)).carrier
          (stageCut F K s (n+1)),
        stageLt F K (n+1) x.val y.val ↔
          stageLt F K (m+1) (T x) (T y)) ∧
      (stage F K (m+1)).graph.toPredimension.IsDClosed
        ((Finset.univ : Finset
          (SupportCarrier (stage F K (n+1)).carrier
            (stageCut F K s (n+1)))).image T) Finset.univ ∧
      (∀ x : SupportCarrier (stage F K (n+1)).carrier
          (stageCut F K s (n+1)),
        (cutOldBirthBValue F K s (n+1) x).image T =
          stageOldBirthBValue F K (m+1) (T x)) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  let h := actualCutTransport F K s hs n m e he hAdj hOldClosed
  have hGraph := actualCutLift_oneLevel F K s hs n m
    e he hAdj hOldClosed
  rcases hGraph with ⟨hInj, hInduced, hOrder, hClosed⟩
  refine ⟨hInj, hInduced, hOrder, hClosed, ?_⟩
  intro x
  exact selectedCutOneStepLift_completeActualBirthBValues
    F K s hs n m e he h hOldBirth x

end CFCoherentTower
end BigHrushovski
