import BigHrushovski.CFGapThenOneLevelCompleteFunctional
import BigHrushovski.CFInitialSelectedCut

/-!
# Iterating genuine C_F finite selected-cut embeddings

The finite source need only be mapped on the selected old stage cut.
This record packages exactly the four hypotheses needed for the next
represented birth-level step. It uses the COMPLETE actual finite
birth-b-values, not a surrogate support operation.

The initial selected cut has no vertices when no source birth level
precedes it. The next-cut constructor handles arbitrary gaps without
a map on the full ambient source stage.

A finite list of certified represented-level gaps can therefore be
realized by induction. This is not yet a proof that every arbitrary
strictly increasing assignment of represented levels supplies such
a certificate, nor a proof of uniqueness.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- A concrete map on the actual source cut satisfying the exact
structural and functional invariant needed for the next level. -/
structure VerifiedCutMap
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ) where
  toFun : SupportCarrier (stage F K n).carrier
    (stageCut F K s n) → (stage F K p).carrier
  strictMono :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K p).carrier :=
      stageLinearOrder F K p
    StrictMono toFun
  induced : ∀ u v : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
    (stage F K n).graph.adj u.val v.val ↔
      (stage F K p).graph.adj (toFun u) (toFun v)
  closed : (stage F K p).graph.toPredimension.IsDClosed
    (selectedOldImage (stageCut F K s n) toFun) Finset.univ
  birthBValues : ∀ u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n),
    (cutOldBirthBValue F K s n u).image toFun =
      stageOldBirthBValue F K p (toFun u)

namespace VerifiedCutMap

/-- Any verified cut map is injective, without an additional
injectivity axiom on its selected source carrier. -/
theorem injective
    {F : ℕ → ℝ} {K : ℕ → ℕ} {s : Finset (Vertex F K)}
    {n p : ℕ} (h : VerifiedCutMap F K s n p) :
    Function.Injective h.toFun := by
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K p).carrier := stageLinearOrder F K p
  exact h.strictMono.injective

/-- Exact complete finite birth-values also give exact transport
of the literal countable birth-labelled operation. -/
theorem completeBirthImage
    {F : ℕ → ℝ} {K : ℕ → ℕ} {s : Finset (Vertex F K)}
    {n p : ℕ} (h : VerifiedCutMap F K s n p)
    (u : SupportCarrier (stage F K n).carrier
      (stageCut F K s n)) :
    (cutOldBirthBValue F K s n u).image
      (fun w => toVertex F K p (h.toFun w)) =
    birthBValue F K (toVertex F K p (h.toFun u)) := by
  calc
    (cutOldBirthBValue F K s n u).image
        (fun w => toVertex F K p (h.toFun w)) =
      ((cutOldBirthBValue F K s n u).image h.toFun).image
        (toVertex F K p) := by
          rw [Finset.image_image]
          rfl
    _ = (stageOldBirthBValue F K p (h.toFun u)).image
        (toVertex F K p) := by rw [h.birthBValues u]
    _ = birthBValue F K (toVertex F K p (h.toFun u)) :=
      stageOldBirthBValue_image F K p (h.toFun u)

/-- At a source stage preceding every source birth level, the
unique empty selected map into any target stage has all invariants,
including absolute strict d-closedness and full birth-values. -/
noncomputable def initial
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) (n p : ℕ)
    (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
    VerifiedCutMap F K s n p := by
  refine ⟨initialCutOldMap F K s n p hNoEarlier,
    initialCutOldMap_strictMono F K s n p hNoEarlier,
    initialCutOldMap_induced F K s n p hNoEarlier,
    initialCutOldMap_dClosed F K s n p hNoEarlier, ?_⟩
  intro u
  exact (initialCut_noOldVertex F K s n hNoEarlier u).elim

/-- Advance an actual selected cut across unrepresented source
levels and arbitrary target-stage gaps, then add the full selected
blocks at the next represented source level. -/
noncomputable def next
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ) :
    VerifiedCutMap F K s (m+1) (p+k+1) := by
  have hFull := gapThenOneLevelMap_completeFunctional F K s hs
    n m hnm hGap p k h.toFun
    h.strictMono h.induced h.closed h.birthBValues
  rcases hFull with ⟨_, hAdj, hOrder, hClosed, hValues⟩
  refine
    { toFun := gapThenOneLevelMap F K s hs n m hnm hGap p k
        h.toFun h.strictMono h.induced h.closed
      strictMono := ?_
      induced := ?_
      closed := ?_
      birthBValues := ?_ }
  · letI : LinearOrder (stage F K (m+1)).carrier :=
      stageLinearOrder F K (m+1)
    letI : LinearOrder (stage F K (p+k+1)).carrier :=
      stageLinearOrder F K (p+k+1)
    intro u v huv
    change stageLt F K (m+1) u.val v.val at huv
    exact (hOrder u v).mp huv
  · exact hAdj
  · exact hClosed
  · exact hValues

/-- The next map agrees literally with the old map on each
previously selected vertex after canonical source-cut inclusion. -/
theorem next_oldBirthExact
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ)
    (u : SupportCarrier (stage F K n).carrier (stageCut F K s n)) :
    toVertex F K (p+k+1)
      ((h.next hs m hnm hGap k).toFun
        (selectedCutEquiv F K s hs m
          (Sum.inl (stageCutGapEquiv F K s n m hnm hGap u)))) =
    toVertex F K p (h.toFun u) := by
  exact gapThenOneLevelMap_oldBirthExact F K s hs n m hnm
    hGap p k h.toFun h.strictMono h.induced h.closed u

/-- Every selected fresh source vertex has precisely the new
target birth level; no separation of target levels is required. -/
theorem next_freshBirthLevel
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)} {n p : ℕ}
    (h : VerifiedCutMap F K s n p)
    (hs : IsBirthBlockClosed F K s)
    (m : ℕ) (hnm : n ≤ m)
    (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
    (k : ℕ)
    (r : SelectedRequests (stage F K m).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedRequests F K s m))
    (i : Fin r.val.code.1.val) :
    (toVertex F K (p+k+1)
      ((h.next hs m hnm hGap k).toFun
        (selectedCutEquiv F K s hs m (Sum.inr ⟨r, i⟩)))).1 =
      p+k := by
  exact gapThenOneLevelMap_freshBirthLevel F K s hs n m hnm
    hGap p k h.toFun h.strictMono h.induced h.closed r i

end VerifiedCutMap

/-- A finite sequence of source levels with explicitly certified
unrepresented gaps and prescribed target-stage jumps. The first
source cut is empty; later cuts are genuine dependent finite
subtypes, not abstract renumberings of the source. -/
inductive RepresentedLevelPlan
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : ℕ → ℕ → Type where
  | initial (n p : ℕ) (hNoEarlier : ∀ v ∈ s, n ≤ v.1) :
      RepresentedLevelPlan F K s n p
  | step {n p : ℕ} (prev : RepresentedLevelPlan F K s n p)
      (m : ℕ) (hnm : n ≤ m)
      (hGap : ∀ i ∈ representedLevels F K s, i < n ∨ m ≤ i)
      (k : ℕ) :
      RepresentedLevelPlan F K s (m+1) (p+k+1)

namespace RepresentedLevelPlan

/-- Every finite certified sequence of represented source levels
has a concrete induced, increasing, strictly d-closed map
preserving ALL complete actual finite and countable birth-values.
The construction is by induction on this finite sequence. -/
noncomputable def lift
    {F : ℕ → ℝ} {K : ℕ → ℕ}
    {s : Finset (Vertex F K)}
    (hs : IsBirthBlockClosed F K s)
    {n p : ℕ} (plan : RepresentedLevelPlan F K s n p) :
    VerifiedCutMap F K s n p := by
  induction plan with
  | initial n p hNoEarlier =>
      exact VerifiedCutMap.initial F K s n p hNoEarlier
  | step prev m hnm hGap k ih =>
      exact ih.next hs m hnm hGap k

end RepresentedLevelPlan

end CFCoherentTower
end BigHrushovski
