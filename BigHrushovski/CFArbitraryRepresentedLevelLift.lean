import BigHrushovski.CFVerifiedCutGapTransport

/-!
# Finite C_F lifting for arbitrary increasing represented-level assignments

A finite birth-block-closed source meets only finitely many birth
levels. An increasing assignment of THOSE levels to target levels
need not extend to a strictly increasing map on all of ℕ.

We instead recurse over the ambient source stages. The target old
stage is the successor of the last assigned represented level, or
zero if none has occurred. If a source level is not represented,
the actual source cut is transported without creating any new block.
At a represented source level, the automatic one-level constructor
places all selected fresh blocks at precisely the prescribed target
level. Its old target stage is no later than the requested level
because the assignment is increasing on represented levels.

The resulting maps are on genuine selected finite source cuts,
and preserve the complete actual birth-b-values, induced adjacency,
the inherited finite-stage order, and strict d-closedness in the
entire target stage. This proves EXISTENCE of finite level lifts;
uniqueness among arbitrary functional embeddings is separate.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Strict increase is required ONLY between birth levels represented
in the finite source. Nothing is required at unused source levels. -/
def StrictOnRepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ) : Prop :=
  ∀ i ∈ representedLevels F K s,
    ∀ j ∈ representedLevels F K s,
      i < j → h i < h j

/-- The old target stage after processing source levels before n.
At represented levels it is exactly one greater than the assigned
target birth level; at unused source levels it stays unchanged. -/
noncomputable def assignedTargetStage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 =>
      if n ∈ representedLevels F K s then h n + 1
      else assignedTargetStage F K s h n

@[simp] theorem assignedTargetStage_zero
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ) :
    assignedTargetStage F K s h 0 = 0 := rfl

theorem assignedTargetStage_succ_of_mem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ)
    (n : ℕ) (hn : n ∈ representedLevels F K s) :
    assignedTargetStage F K s h (n+1) = h n+1 := by
  simp [assignedTargetStage, hn]

theorem assignedTargetStage_succ_of_not_mem
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ)
    (n : ℕ) (hn : n ∉ representedLevels F K s) :
    assignedTargetStage F K s h (n+1) =
      assignedTargetStage F K s h n := by
  simp [assignedTargetStage, hn]

/-- The available old target stage never exceeds the target
birth level prescribed for any remaining represented source level.
This finite-order estimate is what makes consecutive target
levels admissible without any separation or global increasing
self-map of ℕ. -/
theorem assignedTargetStage_le_of_later
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (h : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) :
    ∀ i ∈ representedLevels F K s,
      n ≤ i → assignedTargetStage F K s h n ≤ h i := by
  induction n with
  | zero =>
      intro i hi hle
      simp
  | succ n ih =>
      intro i hi hle
      by_cases hn : n ∈ representedLevels F K s
      · have hni : n < i := by omega
        have hTarget : h n < h i :=
          hStrict n hn i hi hni
        rw [assignedTargetStage_succ_of_mem F K s h n hn]
        omega
      · rw [assignedTargetStage_succ_of_not_mem F K s h n hn]
        exact ih i hi (by omega)

/-- A genuinely partial, complete functional C_F lift at EVERY
source stage, for an arbitrary increasing assignment of its
represented levels. No a priori certificates or global Nat
endomorphism are assumed. -/
noncomputable def finiteLevelCutLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) :
    VerifiedCutMap F K s n (assignedTargetStage F K s h n) := by
  induction n with
  | zero =>
      simpa only [assignedTargetStage_zero] using
        (VerifiedCutMap.initial F K s 0 0 (by
          intro v hv
          exact Nat.zero_le v.1))
  | succ n ih =>
      by_cases hn : n ∈ representedLevels F K s
      · have hGap :
            ∀ i ∈ representedLevels F K s,
              i < n ∨ n ≤ i := by
          intro i hi
          exact lt_or_ge i n
        have hpq : assignedTargetStage F K s h n ≤ h n :=
          assignedTargetStage_le_of_later
            F K s h hStrict n n hn (Nat.le_refl n)
        have hNext := ih.nextAtTarget hs n (Nat.le_refl n)
          hGap (h n) hpq
        simpa only [assignedTargetStage_succ_of_mem F K s h n hn]
          using hNext
      · have hGap :
            ∀ i ∈ representedLevels F K s,
              i < n ∨ n+1 ≤ i := by
          intro i hi
          by_cases hlt : i < n
          · exact Or.inl hlt
          · right
            have hne : i ≠ n := by
              intro heq
              subst i
              exact hn hi
            omega
        have hNext := ih.acrossGap hs (n+1)
          (Nat.le_succ n) hGap 0
        simpa only [assignedTargetStage_succ_of_not_mem F K s h n hn,
          Nat.add_zero] using hNext

/-- At a represented level n, the actual successor cut has a
complete functional induced lift into EXACTLY target stage
U_(h(n)+1). In particular no extra target-level separation
is needed between consecutive represented levels. -/
noncomputable def finiteLevelLift_afterRepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s h)
    (n : ℕ) (hn : n ∈ representedLevels F K s) :
    VerifiedCutMap F K s (n+1) (h n+1) := by
  simpa only [assignedTargetStage_succ_of_mem F K s h n hn] using
    (finiteLevelCutLift F K s hs h hStrict (n+1))

/-- The arbitrary-level lift sends every vertex in the actual
finite source cut to a target vertex with the exact complete
actual countable birth-b-value. -/
theorem finiteLevelCutLift_completeBirthImage
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s h)
    (n : ℕ)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    (cutOldBirthBValue F K s n u).image
      (fun w => toVertex F K (assignedTargetStage F K s h n)
        ((finiteLevelCutLift F K s hs h hStrict n).toFun w)) =
      birthBValue F K
        (toVertex F K (assignedTargetStage F K s h n)
          ((finiteLevelCutLift F K s hs h hStrict n).toFun u)) := by
  exact (finiteLevelCutLift F K s hs h hStrict n).completeBirthImage u

end CFCoherentTower
end BigHrushovski
