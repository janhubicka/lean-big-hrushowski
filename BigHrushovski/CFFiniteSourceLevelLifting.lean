import BigHrushovski.CFArbitraryRepresentedLevelLift
import BigHrushovski.CFCountableGrowth

/-!
# From the actual finite C_F source cuts to the whole finite source

Every finite birth-labelled source lies in some complete finite
stage. The literal selected cut in such a stage has exactly the
original vertices of the source, with no unnamed copy. Its unique
stage representative gives a canonical equivalence.

Combining this equivalence with the arbitrary represented-level
construction produces a genuine map of ALL vertices of the finite
source into the countable birth carrier. The map is injective,
induced on both edges and nonedges, and preserves the full finite
restriction of the actual countable birth-b-value ONTO its target
birth-b-value.

This is the EXISTENCE of a concrete finite graph/b-value lift.
Recovering every prescribed vertex's exact target birth level,
the canonical ordered root/support presentation and uniqueness
among arbitrary functional embeddings remain distinct obligations.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- After a sufficiently large stage, the literal finite
source cut is the ENTIRE given source, not merely a subset. -/
theorem finiteSource_is_stageCut_birthImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    ∃ n : ℕ,
      (stageCut F K s n).image (toVertex F K n) = s := by
  classical
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  refine ⟨n, ?_⟩
  rw [stageCut_birthImage_eq_filter]
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact (mem_stageImage_iff_birth_lt F K n v).mp (hCover hv)

/-- The actual finite source is canonically equivalent to the
selected subtype of any stage covering its birth vertices.
The equivalence literally retains each birth-labelled vertex. -/
noncomputable def finiteSourceCutEquiv
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hCover : s ⊆ stageImage F K n) :
    SupportCarrier (stage F K n).carrier (stageCut F K s n) ≃
      SupportCarrier (Vertex F K) s := by
  classical
  let e : SupportCarrier (stage F K n).carrier
      (stageCut F K s n) →
      SupportCarrier (Vertex F K) s :=
    fun u => ⟨toVertex F K n u.val,
      (mem_stageCut_iff F K s n u.val).mp u.property⟩
  have heInj : Function.Injective e := by
    intro u v huv
    apply Subtype.ext
    apply toVertex_injective F K n
    exact congrArg Subtype.val huv
  have heSurj : Function.Surjective e := by
    intro v
    obtain ⟨u, _, huv⟩ := Finset.mem_image.mp (hCover v.property)
    have hu : u ∈ stageCut F K s n :=
      (mem_stageCut_iff F K s n u).mpr (by
        rw [huv]
        exact v.property)
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext huv
  exact Equiv.ofBijective e ⟨heInj, heSurj⟩

/-- The canonical cut equivalence is the identity on the
literal countable birth-labelled vertex set. -/
theorem finiteSourceCutEquiv_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    (finiteSourceCutEquiv F K s n hCover u).val =
      toVertex F K n u.val := rfl

/-- The inverse cut equivalence returns the uniquely correct
finite-stage representative of each original birth vertex. -/
theorem finiteSourceCutEquiv_symm_birth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n : ℕ)
    (hCover : s ⊆ stageImage F K n)
    (v : SupportCarrier (Vertex F K) s) :
    toVertex F K n
      ((finiteSourceCutEquiv F K s n hCover).symm v).val = v.val := by
  let E := finiteSourceCutEquiv F K s n hCover
  calc
    toVertex F K n (E.symm v).val = (E (E.symm v)).val :=
      (finiteSourceCutEquiv_birth F K s n hCover (E.symm v)).symm
    _ = v.val := congrArg Subtype.val (E.apply_symm_apply v)

/-- The birth-b-value of a finite closed source vertex,
pulled back to the FULL finite source subtype, retains its
whole old support and whole fresh block. -/
noncomputable def finiteSourceBirthBValue
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (v : SupportCarrier (Vertex F K) s) :
    Finset (SupportCarrier (Vertex F K) s) := by
  classical
  exact Finset.univ.filter (fun w =>
    w.val ∈ birthBValue F K v.val)

/-- Closedness of the finite source guarantees that the
finite-source b-value contains EVERY actual birth-b-value vertex. -/
theorem finiteSourceBirthBValue_image
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (v : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s v).image Subtype.val =
      birthBValue F K v.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    rw [← huw]
    exact (Finset.mem_filter.mp hu).2
  · intro hw
    have hws : w ∈ s :=
      birthBValue_subset_of_closed F K s hs v.property hw
    apply Finset.mem_image.mpr
    refine ⟨⟨w, hws⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩

/-- The old-stage complete finite b-value is precisely the
preimage of the same function on the whole actual source subtype. -/
theorem finiteSourceCutEquiv_bValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x : SupportCarrier (Vertex F K) s) :
    (cutOldBirthBValue F K s n
      ((finiteSourceCutEquiv F K s n hCover).symm x)).image
        (finiteSourceCutEquiv F K s n hCover) =
      finiteSourceBirthBValue F K s x := by
  classical
  let E := finiteSourceCutEquiv F K s n hCover
  let u := E.symm x
  apply Finset.image_injective (Subtype.val_injective)
  calc
    ((cutOldBirthBValue F K s n u).image E).image Subtype.val =
      (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K n w.val) := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro w hw
          exact finiteSourceCutEquiv_birth F K s n hCover w
    _ = birthBValue F K (toVertex F K n u.val) :=
      cutOldBirthBValue_image F K s hs n u
    _ = birthBValue F K x.val := by
      rw [finiteSourceCutEquiv_symm_birth F K s n hCover x]
    _ = (finiteSourceBirthBValue F K s x).image Subtype.val :=
      (finiteSourceBirthBValue_image F K s hs x).symm

/-- A map defined on the WHOLE prescribed finite source by
transporting the actual selected-cut map through the canonical
source-cut equivalence. There is no total map of unused source
stage vertices into the target stage. -/
noncomputable def finiteSourceLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    SupportCarrier (Vertex F K) s → Vertex F K :=
  fun x => toVertex F K (assignedTargetStage F K s h n)
    ((finiteLevelCutLift F K s hs h hStrict n).toFun
      ((finiteSourceCutEquiv F K s n hCover).symm x))

/-- The whole finite source lift is injective, with no
unproved extension or arbitrary choice of ambient old-stage map. -/
theorem finiteSourceLift_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    Function.Injective (finiteSourceLift F K s hs h hStrict n hCover) := by
  let E := finiteSourceCutEquiv F K s n hCover
  let M := finiteLevelCutLift F K s hs h hStrict n
  intro x y hxy
  have hTarget : M.toFun (E.symm x) = M.toFun (E.symm y) :=
    (toVertex_injective F K (assignedTargetStage F K s h n)) hxy
  have hSource : E.symm x = E.symm y := M.injective hTarget
  exact E.symm.injective hSource

/-- The whole finite lift is induced on edges AND nonedges
of the original countable C_F graph. -/
theorem finiteSourceLift_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x y : SupportCarrier (Vertex F K) s) :
    (countableGraph F K).adj x.val y.val ↔
      (countableGraph F K).adj
        (finiteSourceLift F K s hs h hStrict n hCover x)
        (finiteSourceLift F K s hs h hStrict n hCover y) := by
  let E := finiteSourceCutEquiv F K s n hCover
  let M := finiteLevelCutLift F K s hs h hStrict n
  change (countableGraph F K).adj x.val y.val ↔
    (countableGraph F K).adj
      (toVertex F K (assignedTargetStage F K s h n)
        (M.toFun (E.symm x)))
      (toVertex F K (assignedTargetStage F K s h n)
        (M.toFun (E.symm y)))
  calc
    (countableGraph F K).adj x.val y.val ↔
      (stage F K n).graph.adj (E.symm x).val (E.symm y).val := by
        rw [← finiteSourceCutEquiv_symm_birth F K s n hCover x,
          ← finiteSourceCutEquiv_symm_birth F K s n hCover y]
        exact (countableGraph_stage_induced F K n _ _).symm
    _ ↔ (stage F K (assignedTargetStage F K s h n)).graph.adj
      (M.toFun (E.symm x)) (M.toFun (E.symm y)) :=
        M.induced (E.symm x) (E.symm y)
    _ ↔ (countableGraph F K).adj
      (toVertex F K (assignedTargetStage F K s h n)
        (M.toFun (E.symm x)))
      (toVertex F K (assignedTargetStage F K s h n)
        (M.toFun (E.symm y))) :=
          countableGraph_stage_induced F K (assignedTargetStage F K s h n)
            (M.toFun (E.symm x)) (M.toFun (E.symm y))

/-- Every COMPLETE birth-b-value of the whole original finite
source is carried ONTO the literal complete target birth-b-value. -/
theorem finiteSourceLift_birthBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceBirthBValue F K s x).image
      (finiteSourceLift F K s hs h hStrict n hCover) =
      birthBValue F K
        (finiteSourceLift F K s hs h hStrict n hCover x) := by
  classical
  let E := finiteSourceCutEquiv F K s n hCover
  let M := finiteLevelCutLift F K s hs h hStrict n
  let u := E.symm x
  have hSource :
      (cutOldBirthBValue F K s n u).image E =
        finiteSourceBirthBValue F K s x :=
    finiteSourceCutEquiv_bValues F K s hs n hCover x
  calc
    (finiteSourceBirthBValue F K s x).image
        (finiteSourceLift F K s hs h hStrict n hCover) =
      ((cutOldBirthBValue F K s n u).image E).image
        (finiteSourceLift F K s hs h hStrict n hCover) := by
          rw [hSource]
    _ = (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K (assignedTargetStage F K s h n)
          (M.toFun w)) := by
          rw [Finset.image_image]
          apply Finset.image_congr
          intro w hw
          change toVertex F K (assignedTargetStage F K s h n)
            (M.toFun (E.symm (E w))) =
            toVertex F K (assignedTargetStage F K s h n)
              (M.toFun w)
          rw [Equiv.symm_apply_apply]
    _ = birthBValue F K
        (toVertex F K (assignedTargetStage F K s h n)
          (M.toFun u)) := M.completeBirthImage u
    _ = birthBValue F K
        (finiteSourceLift F K s hs h hStrict n hCover x) := rfl

/-- Every finite birth-block-closed C_F source admits an actual
injective induced graph/b-value embedding into the countable
C_F presentation under any strictly increasing assignment of
its represented levels. This is an EXISTENCE theorem, not
unique level lifting. -/
theorem finiteSourceLift_exists
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hStrict : StrictOnRepresented F K s h) :
    ∃ f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image f =
          birthBValue F K (f x)) := by
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let f := finiteSourceLift F K s hs h hStrict n hCover
  refine ⟨f, finiteSourceLift_injective F K s hs h hStrict n hCover,
    ?_, ?_⟩
  · intro x y
    exact finiteSourceLift_induced F K s hs h hStrict n hCover x y
  · intro x
    exact finiteSourceLift_birthBValues F K s hs h hStrict n hCover x

end CFCoherentTower
end BigHrushovski
