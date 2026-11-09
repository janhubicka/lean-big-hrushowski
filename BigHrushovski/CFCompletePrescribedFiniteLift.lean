import BigHrushovski.CFPrescribedBirthLevelLifting

/-!
# Finite C_F existence with exact prescribed represented levels

The earlier cut-map construction and whole-source equivalence
give a reusable transport theorem: ANY complete verified finite
selected-cut map extends canonically to all original finite source
vertices, preserving the induced graph and complete birth-b-values.

Apply it to the strengthened recursive map carrying the literal
prescribed birth-level invariant. This gives ONE embedding of the
entire finite b-closed source for every strictly increasing target
assignment on its represented source levels. It does not yet prove
uniqueness among arbitrary functional embeddings.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Transport an arbitrary verified actual selected-cut embedding
back to the original finite birth-labelled source vertex set. -/
noncomputable def finiteSourceLiftOfCut
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (M : VerifiedCutMap F K s n p) :
    SupportCarrier (Vertex F K) s → Vertex F K :=
  fun x => toVertex F K p
    (M.toFun ((finiteSourceCutEquiv F K s n hCover).symm x))

theorem finiteSourceLiftOfCut_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (M : VerifiedCutMap F K s n p) :
    Function.Injective (finiteSourceLiftOfCut F K s n p hCover M) := by
  let E := finiteSourceCutEquiv F K s n hCover
  intro x y hxy
  have hTarget : M.toFun (E.symm x) = M.toFun (E.symm y) :=
    (toVertex_injective F K p) hxy
  exact E.symm.injective (M.injective hTarget)

theorem finiteSourceLiftOfCut_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (M : VerifiedCutMap F K s n p)
    (x y : SupportCarrier (Vertex F K) s) :
    (countableGraph F K).adj x.val y.val ↔
      (countableGraph F K).adj
        (finiteSourceLiftOfCut F K s n p hCover M x)
        (finiteSourceLiftOfCut F K s n p hCover M y) := by
  let E := finiteSourceCutEquiv F K s n hCover
  change (countableGraph F K).adj x.val y.val ↔
    (countableGraph F K).adj
      (toVertex F K p (M.toFun (E.symm x)))
      (toVertex F K p (M.toFun (E.symm y)))
  calc
    (countableGraph F K).adj x.val y.val ↔
      (stage F K n).graph.adj (E.symm x).val (E.symm y).val := by
        rw [← finiteSourceCutEquiv_symm_birth F K s n hCover x,
          ← finiteSourceCutEquiv_symm_birth F K s n hCover y]
        exact (countableGraph_stage_induced F K n _ _).symm
    _ ↔ (stage F K p).graph.adj
      (M.toFun (E.symm x)) (M.toFun (E.symm y)) :=
        M.induced (E.symm x) (E.symm y)
    _ ↔ (countableGraph F K).adj
      (toVertex F K p (M.toFun (E.symm x)))
      (toVertex F K p (M.toFun (E.symm y))) :=
        countableGraph_stage_induced F K p _ _

/-- Whole-source preservation of the actual complete birth-b-value
is a generic consequence of exact finite selected-cut values. -/
theorem finiteSourceLiftOfCut_birthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n p : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (M : VerifiedCutMap F K s n p)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
      (finiteSourceLiftOfCut F K s n p hCover M) =
      birthBValue F K (finiteSourceLiftOfCut F K s n p hCover M x) := by
  classical
  let E := finiteSourceCutEquiv F K s n hCover
  let u := E.symm x
  have hSource :
      (cutOldBirthBValue F K s n u).image E =
        finiteSourceBirthBValue F K s x :=
    finiteSourceCutEquiv_bValues F K s hs n hCover x
  calc
    (finiteSourceBirthBValue F K s x).image
        (finiteSourceLiftOfCut F K s n p hCover M) =
      ((cutOldBirthBValue F K s n u).image E).image
        (finiteSourceLiftOfCut F K s n p hCover M) := by
          rw [hSource]
    _ = (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K p (M.toFun w)) := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro w hw
          change toVertex F K p (M.toFun (E.symm (E w))) =
            toVertex F K p (M.toFun w)
          rw [Equiv.symm_apply_apply]
    _ = birthBValue F K (toVertex F K p (M.toFun u)) :=
      M.completeBirthImage u
    _ = birthBValue F K
        (finiteSourceLiftOfCut F K s n p hCover M x) := rfl

/-- The birth-aware recursive lift, transported to all original
finite source vertices. -/
noncomputable def finiteSourcePrescribedLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    SupportCarrier (Vertex F K) s → Vertex F K :=
  finiteSourceLiftOfCut F K s n (assignedTargetStage F K s level n)
    hCover (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map

theorem finiteSourcePrescribedLift_birthLevel
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourcePrescribedLift
      F K s hs level hStrict n hCover x).1 = level x.val.1 := by
  let E := finiteSourceCutEquiv F K s n hCover
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  change (toVertex F K (assignedTargetStage F K s level n)
    (M.map.toFun (E.symm x))).1 = level x.val.1
  calc
    (toVertex F K (assignedTargetStage F K s level n)
      (M.map.toFun (E.symm x))).1 =
      level (toVertex F K n (E.symm x).val).1 :=
        M.birthLevel (E.symm x)
    _ = level x.val.1 := by
      rw [finiteSourceCutEquiv_symm_birth F K s n hCover x]

/-- Existence on the ENTIRE finite b-closed source with induced
edges/nonedges, complete birth-b-values, and the EXACT prescribed
target birth level of each original vertex. No target-level
separation or global increasing Nat self-map is required. -/
theorem finiteSourcePrescribedLift_exists
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
        (f x).1 = level x.val.1) := by
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let M := finiteLevelCutLiftWithBirth F K s hs level hStrict n
  let f := finiteSourcePrescribedLift
    F K s hs level hStrict n hCover
  refine ⟨f, ?_, ?_, ?_, ?_⟩
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

end CFCoherentTower
end BigHrushovski
