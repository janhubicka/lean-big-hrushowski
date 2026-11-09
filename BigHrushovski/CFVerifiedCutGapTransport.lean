import BigHrushovski.CFVerifiedCutInduction

/-!
# Reusable partial C_F source-gap transport and prescribed target levels

The full finite selected-cut invariant can be transported across a
source interval containing no represented level, without introducing
a fresh block. An arbitrary target-stage ascent may be performed
simultaneously. The domain remains the actual later finite source cut.

The same invariant also extends over the next represented source
level at a prescribed target birth level q, whenever the existing
target old stage p is no later than q. No target-level separation
beyond strict increase of the *represented* levels is needed.

These are local induction interfaces; the global finite
represented-level enumeration and arbitrary-embedding uniqueness
remain separate statements.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

namespace VerifiedCutMap

/-- Transport the entire actual old selected finite source
across an unrepresented interval and ascend the old target by k
levels, without adding a new target block. -/
noncomputable def acrossGap
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ) :
    VerifiedCutMap F K s m (p+k) := by
  let eGap := sourceTargetGapMap F K s n m hnm hGap
    p k h.toFun
  refine
    { toFun := eGap
      strictMono := ?_
      induced := ?_
      closed := ?_
      birthBValues := ?_ }
  · exact sourceTargetGapMap_strictMono F K s n m hnm hGap
      p k h.toFun h.strictMono
  · intro u v
    exact sourceTargetGapMap_induced F K s n m hnm hGap
      p k h.toFun h.induced u v
  · exact sourceTargetGapMap_dClosed F K s n m hnm hGap
      p k h.toFun h.closed
  · intro u
    exact sourceTargetGapMap_completeBirthBValues
      F K s hs n m hnm hGap p k h.toFun h.birthBValues u

/-- On every actual old source vertex the transported map retains
the literal countable target birth vertex, with no relabelling. -/
theorem acrossGap_oldBirthExact
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    toVertex F K (p+k)
      ((h.acrossGap hs m hnm hGap k).toFun
        (stageCutGapEquiv F K s n m hnm hGap u)) =
    toVertex F K p (h.toFun u) := by
  change toVertex F K (p+k)
      (ascend F K p k
        (h.toFun
          ((stageCutGapEquiv F K s n m hnm hGap).symm
            (stageCutGapEquiv F K s n m hnm hGap u)))) =
    toVertex F K p (h.toFun u)
  rw [Equiv.symm_apply_apply]
  exact toVertex_ascend F K p k (h.toFun u)

/-- Choose the target birth level q directly, instead of
supplying a non-canonical subtraction parameter k.
The old target stage p need only satisfy p ≤ q. -/
noncomputable def nextAtTarget
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (q : ℕ) (hpq : p ≤ q) :
    VerifiedCutMap F K s (m+1) (q+1) := by
  simpa only [Nat.add_sub_of_le hpq] using
    (h.next hs m hnm hGap (q-p))

/-- A new block is born at exactly the prescribed target level q
under the direct target-level interface. -/
theorem nextAtTarget_freshBirthLevel
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (q : ℕ) (hpq : p ≤ q)
    (r : SelectedRequests (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s m))
    (i : Fin r.val.code.1.val) :
    (toVertex F K (q+1)
      ((h.nextAtTarget hs m hnm hGap q hpq).toFun
        (selectedCutEquiv F K s hs m (Sum.inr ⟨r, i⟩)))).1 =
      q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  simpa [nextAtTarget, Nat.add_sub_cancel_left] using
    (h.next_freshBirthLevel hs m hnm hGap k r i)

/-- Old vertices retain their previously assigned literal target
birth labels, independent of the choice of the new level q. -/
theorem nextAtTarget_oldBirthExact
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (q : ℕ) (hpq : p ≤ q)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    toVertex F K (q+1)
      ((h.nextAtTarget hs m hnm hGap q hpq).toFun
        (selectedCutEquiv F K s hs m
          (Sum.inl (stageCutGapEquiv F K s n m hnm hGap u)))) =
    toVertex F K p (h.toFun u) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  simpa [nextAtTarget, Nat.add_sub_cancel_left] using
    (h.next_oldBirthExact hs m hnm hGap k u)

end VerifiedCutMap
end CFCoherentTower
end BigHrushovski
