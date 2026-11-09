import BigHrushovski.CFFiniteSourceLevelLifting

/-!
# Exact prescribed target birth levels for finite C_F lifts

A complete finite cut map preserves all graph and birth-b-value
data, but its record alone does not assert the target birth level
of each individual old vertex. We track that assertion as a
separate invariant of the recursive construction.

Unrepresented source levels carry the literal source and target
birth labels unchanged. A new represented source level is sent to
the requested target level, while every previously mapped vertex
retains its assigned target birth identity. Thus a strictly
increasing assignment on only the finitely represented source
levels determines a partial map with the EXACT assigned birth
level for every vertex of every selected cut.

This proves the level-label part of existence. Intrinsic uniqueness
among arbitrary functional embeddings remains to be proved.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A verified finite cut embedding whose target birth level is
literally the prescribed value on EVERY selected source vertex. -/
structure PrescribedBirthCutMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ) (n p : ℕ) where
  map : VerifiedCutMap F K s n p
  birthLevel :
    ∀ u : SupportCarrier (stage F K n).carrier
        (stageCut F K s n),
      (toVertex F K p (map.toFun u)).1 =
        level (toVertex F K n u.val).1

namespace PrescribedBirthCutMap

/-- The exact birth-level induction invariant holds on the
initial empty selected cut even if the ambient source stage
is nonempty. Here the ambient initial stage is U_0. -/
noncomputable def initial
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ) :
    PrescribedBirthCutMap F K s level 0 0 := by
  have hEmpty : ∀ v ∈ s, 0 ≤ v.1 := by
    intro v hv
    exact Nat.zero_le v.1
  refine ⟨VerifiedCutMap.initial F K s 0 0 hEmpty, ?_⟩
  intro u
  exact (initialCut_noOldVertex F K s 0 hEmpty u).elim

/-- Traversing any unrepresented source gap and arbitrary
target ascent does not alter the actual birth label of any
previously mapped vertex. -/
noncomputable def acrossGap
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)}
    {level : ℕ → ℕ} {n p : ℕ}
    (M : PrescribedBirthCutMap F K s level n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ) :
    PrescribedBirthCutMap F K s level m (p+k) := by
  refine ⟨M.map.acrossGap hs m hnm hGap k, ?_⟩
  intro v
  let E := stageCutGapEquiv F K s n m hnm hGap
  let u := E.symm v
  have hSource : toVertex F K m v.val =
      toVertex F K n u.val := by
    have h := stageCutGapEquiv_birth F K s n m hnm hGap u
    simpa only [u, E, Equiv.apply_symm_apply] using h
  have hTarget :
      toVertex F K (p+k)
        ((M.map.acrossGap hs m hnm hGap k).toFun v) =
      toVertex F K p (M.map.toFun u) := by
    have h := M.map.acrossGap_oldBirthExact hs m hnm hGap k u
    simpa only [u, E, Equiv.apply_symm_apply] using h
  calc
    (toVertex F K (p+k)
        ((M.map.acrossGap hs m hnm hGap k).toFun v)).1 =
      (toVertex F K p (M.map.toFun u)).1 :=
        congrArg Sigma.fst hTarget
    _ = level (toVertex F K n u.val).1 := M.birthLevel u
    _ = level (toVertex F K m v.val).1 := by rw [hSource]

/-- The next represented source layer receives precisely its
assigned target birth level; the old source points keep theirs. -/
noncomputable def nextAtTarget
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)}
    {level : ℕ → ℕ} {n p : ℕ}
    (M : PrescribedBirthCutMap F K s level n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (q : ℕ) (hpq : p ≤ q) (hq : q = level m) :
    PrescribedBirthCutMap F K s level (m+1) (q+1) := by
  refine ⟨M.map.nextAtTarget hs m hnm hGap q hpq, ?_⟩
  intro v
  let E := stageCutGapEquiv F K s n m hnm hGap
  let C := selectedCutEquiv F K s hs m
  obtain ⟨z, rfl⟩ := C.surjective v
  cases z with
  | inl old =>
      let u := E.symm old
      have hTarget :
          toVertex F K (q+1)
            ((M.map.nextAtTarget hs m hnm hGap q hpq).toFun
              (C (Sum.inl old))) =
          toVertex F K p (M.map.toFun u) := by
        have h := M.map.nextAtTarget_oldBirthExact
          hs m hnm hGap q hpq u
        simpa only [u, E, Equiv.apply_symm_apply] using h
      have hSource :
          toVertex F K (m+1) (C (Sum.inl old)).val =
          toVertex F K n u.val := by
        calc
          toVertex F K (m+1) (C (Sum.inl old)).val =
            toVertex F K m old.val := by
              rw [selectedCutEquiv_val]
              change toVertex F K (m+1) (Sum.inl old.val) =
                toVertex F K m old.val
              exact toVertex_old F K m old.val
          _ = toVertex F K n u.val := by
            have h := stageCutGapEquiv_birth
              F K s n m hnm hGap u
            simpa only [u, E, Equiv.apply_symm_apply] using h
      calc
        (toVertex F K (q+1)
          ((M.map.nextAtTarget hs m hnm hGap q hpq).toFun
            (C (Sum.inl old)))).1 =
          (toVertex F K p (M.map.toFun u)).1 :=
            congrArg Sigma.fst hTarget
        _ = level (toVertex F K n u.val).1 :=
          M.birthLevel u
        _ = level (toVertex F K (m+1)
          (C (Sum.inl old)).val).1 := by rw [hSource]
  | inr fresh =>
      rcases fresh with ⟨r, i⟩
      have hTarget :
          (toVertex F K (q+1)
            ((M.map.nextAtTarget hs m hnm hGap q hpq).toFun
              (C (Sum.inr ⟨r, i⟩)))).1 = q :=
        M.map.nextAtTarget_freshBirthLevel
          hs m hnm hGap q hpq r i
      have hSource :
          (toVertex F K (m+1)
            (C (Sum.inr ⟨r, i⟩)).val).1 = m := by
        rw [selectedCutEquiv_val]
        rfl
      calc
        (toVertex F K (q+1)
          ((M.map.nextAtTarget hs m hnm hGap q hpq).toFun
            (C (Sum.inr ⟨r, i⟩)))).1 = q := hTarget
        _ = level m := hq
        _ = level (toVertex F K (m+1)
          (C (Sum.inr ⟨r, i⟩)).val).1 := by rw [hSource]

end PrescribedBirthCutMap

/-- Recursively build a level-preserving actual finite cut
embedding from an arbitrary function strictly increasing
only on source levels which are actually represented. -/
noncomputable def finiteLevelCutLiftWithBirth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) :
    PrescribedBirthCutMap F K s level n
      (assignedTargetStage F K s level n) := by
  induction n with
  | zero =>
      simpa only [assignedTargetStage_zero] using
        (PrescribedBirthCutMap.initial F K s level)
  | succ n ih =>
      by_cases hn : n ∈ representedLevels F K s
      · have hGap :
            ∀ i ∈ representedLevels F K s,
              i < n ∨ n ≤ i := by
          intro i hi
          exact lt_or_ge i n
        have hpq : assignedTargetStage F K s level n ≤ level n :=
          assignedTargetStage_le_of_later F K s level hStrict
            n n hn (Nat.le_refl n)
        have hNext := ih.nextAtTarget hs n (Nat.le_refl n)
          hGap (level n) hpq rfl
        simpa only [assignedTargetStage_succ_of_mem
          F K s level n hn] using hNext
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
        simpa only [assignedTargetStage_succ_of_not_mem
          F K s level n hn, Nat.add_zero] using hNext

/-- At EVERY actual selected source vertex the target has
exactly the prescribed birth level, not just the correct
order relation on birth levels. -/
theorem finiteLevelCutLiftWithBirth_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    (toVertex F K (assignedTargetStage F K s level n)
      ((finiteLevelCutLiftWithBirth F K s hs level hStrict n).map.toFun u)).1 =
      level (toVertex F K n u.val).1 :=
  (finiteLevelCutLiftWithBirth F K s hs level hStrict n).birthLevel u

/-- Pass from the actual sufficiently large source stage cut
to the whole ORIGINAL finite source while retaining every
prescribed target birth label. -/
noncomputable def finiteSourceLiftWithPrescribedBirth
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    SupportCarrier (Vertex F K) s → Vertex F K :=
  fun x => toVertex F K (assignedTargetStage F K s level n)
    ((finiteLevelCutLiftWithBirth F K s hs level hStrict n).map.toFun
      ((finiteSourceCutEquiv F K s n hCover).symm x))

theorem finiteSourceLiftWithPrescribedBirth_exact
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n)
    (x : SupportCarrier (Vertex F K) s) :
    (finiteSourceLiftWithPrescribedBirth
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

end CFCoherentTower
end BigHrushovski
