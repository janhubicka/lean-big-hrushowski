import BigHrushovski.CFPrescribedLevelPreorder
import BigHrushovski.CFStageBirthOrderCoherence

/-!
# Canonical birth order of the actual finite C_F prescribed lift

The canonical strict order on the countable birth-labelled carrier
is exactly the restriction of the recursively inherited order on
each finite stage. The previously constructed verified finite cut
map is strictly increasing on its selected source subtype.

We transport this order along the literal source/cut equivalence
and the target finite-stage birth map. The same finite prescribed
lift simultaneously preserves and reflects:
* induced graph adjacency (including nonedges);
* all complete actual birth-b-values;
* the exact prescribed target birth level of each source vertex;
* the whole birth-level preorder; and
* the manuscript's canonical linear order.

There is no full target-stage extension of the selected old map,
and no global increasing map of natural-number levels. This is
still an existence result; uniqueness remains open.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- Any verified selected finite cut map, transported back to the
literal source birth vertices, preserves and reflects the exact
canonical birth order. This uses the already established finite
stage/birth order coherence, not an unrelated linear ordering. -/
theorem finiteSourceLiftOfCut_canonicalOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (M : VerifiedCutMap F K s n p)
    (x y : SupportCarrier (Vertex F K) s) :
    canonicalBirthLt F K x.val y.val ↔
      canonicalBirthLt F K
        (finiteSourceLiftOfCut F K s n p hCover M x)
        (finiteSourceLiftOfCut F K s n p hCover M y) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K p).carrier :=
    stageLinearOrder F K p
  let E := finiteSourceCutEquiv F K s n hCover
  let u := E.symm x
  let v := E.symm y
  have hStages :
      stageLt F K n u.val v.val ↔
        stageLt F K p (M.toFun u) (M.toFun v) := by
    change u < v ↔ M.toFun u < M.toFun v
    constructor
    · exact M.strictMono
    · intro hTarget
      rcases lt_trichotomy u v with hSource | hEqual | hReverse
      · exact hSource
      · subst v
        exact False.elim (lt_irrefl _ hTarget)
      · exact False.elim (lt_asymm (M.strictMono hReverse) hTarget)
  calc
    canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K
          (toVertex F K n u.val) (toVertex F K n v.val) := by
          rw [finiteSourceCutEquiv_symm_birth F K s n hCover x,
            finiteSourceCutEquiv_symm_birth F K s n hCover y]
    _ ↔ stageLt F K n u.val v.val :=
      (stageLt_iff_canonicalBirthLt F K n u.val v.val).symm
    _ ↔ stageLt F K p (M.toFun u) (M.toFun v) := hStages
    _ ↔ canonicalBirthLt F K
          (finiteSourceLiftOfCut F K s n p hCover M x)
          (finiteSourceLiftOfCut F K s n p hCover M y) := by
          change stageLt F K p (M.toFun u) (M.toFun v) ↔
            canonicalBirthLt F K (toVertex F K p (M.toFun u))
              (toVertex F K p (M.toFun v))
          exact stageLt_iff_canonicalBirthLt F K p
            (M.toFun u) (M.toFun v)

/-- The unique concrete constructed prescribed lift, on the entire
actual finite birth-block-closed source, preserves and reflects the
canonical order. The level assignment is strictly increasing only
at birth levels which actually occur in the finite source. -/
theorem finiteSourcePrescribedLift_canonicalOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x y : SupportCarrier (Vertex F K) s) :
    canonicalBirthLt F K x.val y.val ↔
      canonicalBirthLt F K
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover x)
        (finiteSourcePrescribedLift F K s hs level hStrict n hCover y) := by
  exact finiteSourceLiftOfCut_canonicalOrder F K s n
    (assignedTargetStage F K s level n) hCover
    (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map x y

/-- Complete finite prescribed-level existence in the genuine
canonical ordered birth language, with simultaneous exact
graph/b-values/level-preorder/order preservation. No uniqueness or
R,H transport is asserted at this stage. -/
theorem finiteSourcePrescribedLift_exists_ordered
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃ f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image f =
          birthBValue F K (f x)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (f x).1 = level x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (f x) (f y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (f x) (f y)) := by
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  let f := finiteSourcePrescribedLift F K s hs level hStrict n hCover
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover M.map
  · intro x y
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover M.map x y
  · intro x
    exact finiteSourceLiftOfCut_birthBValues F K s hs n
      (assignedTargetStage F K s level n) hCover M.map x
  · intro x
    exact finiteSourcePrescribedLift_birthLevel
      F K s hs level hStrict n hCover x
  · intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder
      F K s hs level hStrict n hCover x y
  · intro x y
    exact finiteSourcePrescribedLift_canonicalOrder
      F K s hs level hStrict n hCover x y

end CFCoherentTower
end BigHrushovski
