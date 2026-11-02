import BigHrushovski.CFSelectedCutBlockRigidity
import BigHrushovski.CFPartialSupportAutomaticClosure

/-!
# The actual one-level C_F lifting step with automatic support transport

The finite lifting proof requires no independent certificate for
each named new request. An induced strictly increasing embedding of
the *selected old cut* with strictly d-closed target image suffices:
every source support lies in that cut, is d-closed there, and
therefore has a literal d-closed target image.

We construct the canonical map of the ACTUAL next source cut directly
from these old-map hypotheses. The map is injective, induced,
preserves and reflects the inherited finite-stage order, and its
image is strictly d-closed in the entire target next stage.

All hypotheses are restricted to the old selected subtype.
In particular there is no function U_n → U_m or gap assumption.
The complete b-value induction and arbitrary-embedding uniqueness
remain separate proof obligations.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Assemble every target request condition automatically from a
strictly increasing induced old-cut embedding and a closed old image. -/
noncomputable def actualCutTransport
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
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph
      (stageCut F K s n) e (selectedRequests F K s n) := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  exact selectedCut_growthTransport_of_induced_dClosed F K s hs n m
    e he.injective hAdj hOldClosed

/-- The canonical next-cut map no longer takes any per-request
transport certificates as an extra argument. -/
noncomputable def actualCutLift
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
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
    SupportCarrier (stage F K (n+1)).carrier (stageCut F K s (n+1)) →
      (stage F K (m+1)).carrier := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  exact selectedCutOneStepLift F K s hs n m e he
    (actualCutTransport F K s hs n m e he hAdj hOldClosed)

/-- One automatic C_F successor step gives an actual induced,
increasing embedding of the whole literal next cut with strictly
d-closed image in the entire target next stage. No other
hypotheses on the selected source requests are needed. -/
theorem actualCutLift_oneLevel
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
      (selectedOldImage (stageCut F K s n) e) Finset.univ) :
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
            (stageCut F K s (n+1)))).image T) Finset.univ := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  let h := actualCutTransport F K s hs n m e he hAdj hOldClosed
  change Function.Injective (selectedCutOneStepLift F K s hs n m e he h) ∧
    (∀ x y : SupportCarrier (stage F K (n+1)).carrier
        (stageCut F K s (n+1)),
      (stage F K (n+1)).graph.adj x.val y.val ↔
        (stage F K (m+1)).graph.adj
          (selectedCutOneStepLift F K s hs n m e he h x)
          (selectedCutOneStepLift F K s hs n m e he h y)) ∧
    (∀ x y : SupportCarrier (stage F K (n+1)).carrier
        (stageCut F K s (n+1)),
      stageLt F K (n+1) x.val y.val ↔
        stageLt F K (m+1)
          (selectedCutOneStepLift F K s hs n m e he h x)
          (selectedCutOneStepLift F K s hs n m e he h y)) ∧
    (stage F K (m+1)).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset
        (SupportCarrier (stage F K (n+1)).carrier
          (stageCut F K s (n+1)))).image
        (selectedCutOneStepLift F K s hs n m e he h)) Finset.univ
  refine ⟨selectedCutOneStepLift_injective F K s hs n m e he h,
    ?_, ?_, ?_⟩
  · intro x y
    exact selectedCutOneStepLift_induced F K s hs n m e he hAdj h x y
  · intro x y
    exact selectedCutOneStepLift_stageOrder_iff F K s hs n m e he h x y
  · exact selectedCutOneStepLift_dClosed_full F K s hs n m e he h hOldClosed

end CFCoherentTower
end BigHrushovski
