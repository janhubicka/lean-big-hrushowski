import BigHrushovski.CFPrescribedFiniteRHLift

/-!
# Finite inverse level assignments in the actual C_F birth structure

The conditional copy-range equation in the Ellentuck argument needs
a finite *inverse* lift: whenever the complete support of a finite
closed source is contained in the range of an increasing level map h,
we must embed that source at the inverse image of its represented
birth levels.

Track B now gives existence of finite prescribed lifts in the
complete ordered (R,H) language. The only additional arithmetic
ingredient is to choose an inverse to h on its range and prove
that this choice is strictly increasing on the represented
birth levels. No global inverse is required and the source may
have gaps or be empty.

This provides the finite existence step, **not** uniqueness of
arbitrary finite embeddings and not a countable self-embedding.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue

/-- A partial inverse of an arbitrary map on its range, given
an irrelevant default value outside the range. -/
noncomputable def chosenInverseLevel (h : ℕ → ℕ) (q : ℕ) : ℕ :=
  if hq : q ∈ Set.range h then Classical.choose hq else 0

theorem chosenInverseLevel_spec
    (h : ℕ → ℕ) {q : ℕ} (hq : q ∈ Set.range h) :
    h (chosenInverseLevel h q) = q := by
  classical
  simp only [chosenInverseLevel, dif_pos hq]
  exact Classical.choose_spec hq

/-- If h is strictly increasing, its partial inverse is strictly
increasing at all birth levels represented in the finite source,
provided these levels belong to the range of h. No assertion is
made about absent levels. -/
theorem chosenInverseLevel_strictOnRepresented
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hRange : ∀ v ∈ s, v.1 ∈ Set.range h) :
    StrictOnRepresented F K s (chosenInverseLevel h) := by
  classical
  have hRepresented : ∀ q ∈ representedLevels F K s,
      q ∈ Set.range h := by
    intro q hq
    obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
    simpa only [hvq] using hRange v hv
  intro i hi j hj hij
  have hiSpec : h (chosenInverseLevel h i) = i :=
    chosenInverseLevel_spec h (hRepresented i hi)
  have hjSpec : h (chosenInverseLevel h j) = j :=
    chosenInverseLevel_spec h (hRepresented j hj)
  by_contra hNot
  have hBack : chosenInverseLevel h j ≤ chosenInverseLevel h i :=
    Nat.le_of_not_gt hNot
  have hCompare :
      h (chosenInverseLevel h j) ≤ h (chosenInverseLevel h i) :=
    hh.monotone hBack
  omega

/-- One complete ordered finite embedding with *inverse* prescribed
birth levels exists whenever all represented source levels are in
the range of h. This is a finite C_F lift, including complete
b-values, the induced graph, birth-level preorder and canonical order.
It is not a countable embedding and it does not assert uniqueness. -/
theorem finiteClosed_inverseLevelLift_exists
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hRange : ∀ v ∈ s, v.1 ∈ Set.range h) :
    ∃ e : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective e ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (e x) (e y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image e =
          birthBValue F K (e x)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        h ((e x).1) = x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (e x) (e y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (e x) (e y)) := by
  classical
  let level := chosenInverseLevel h
  have hStrict : StrictOnRepresented F K s level :=
    chosenInverseLevel_strictOnRepresented F K s h hh hRange
  obtain ⟨e, heInj, heAdj, heB, heLevel, hePreorder, heOrder⟩ :=
    finiteSourcePrescribedLift_exists_ordered
      F K s hs level hStrict
  refine ⟨e, heInj, heAdj, heB, ?_, hePreorder, heOrder⟩
  intro x
  calc
    h ((e x).1) = h (level x.val.1) := by rw [heLevel x]
    _ = x.val.1 := chosenInverseLevel_spec h (hRange x.val x.property)

/-- The same inverse-level existence map can be chosen to preserve
the complete R(v) and partial H(S) values of the original language.
The extension outside the finite source is used only for evaluating
finite images; it is not asserted to be an embedding there. -/
theorem finiteClosed_inverseRHLift_exists
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (hRange : ∀ v ∈ s, v.1 ∈ Set.range h) :
    ∃ e : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective e ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (e x) (e y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (e x) (e y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (e x) (e y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        h ((e x).1) = x.val.1) ∧
      (let X : Set (Vertex F K) := {v | v ∈ s}
       let f := extendClosedSourceMap F K X e
       (∀ v ∈ X,
         (birthReachableRoots F K v).image f =
           birthReachableRoots F K (f v)) ∧
       (∀ t : Finset (Vertex F K),
         (∀ v ∈ t, v ∈ X) →
         (∀ r ∈ t, IsBirthRoot F K r) →
         (birthDClosedHull F K t).image f =
           birthDClosedHull F K (t.image f)) ∧
       (∀ t : Finset (Vertex F K),
         (∀ v ∈ t, v ∈ X) →
         ((∀ r ∈ t, IsBirthRoot F K r) ↔
           (∀ r ∈ t.image f, IsBirthRoot F K r)))) := by
  classical
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  let level := chosenInverseLevel h
  have hStrict : StrictOnRepresented F K s level :=
    chosenInverseLevel_strictOnRepresented F K s h hh hRange
  let e := finiteSourcePrescribedLift F K s hs level hStrict n hCover
  have heInj : Function.Injective e :=
    finiteSourceLiftOfCut_injective F K s n
      (assignedTargetStage F K s level n) hCover
      (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map
  refine ⟨e, heInj, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact finiteSourceLiftOfCut_induced F K s n
      (assignedTargetStage F K s level n) hCover
      (finiteLevelCutLiftWithBirth F K s hs level hStrict n).map x y
  · intro x y
    exact finiteSourcePrescribedLift_birthLevelPreorder F K s hs
      level hStrict n hCover x y
  · intro x y
    exact finiteSourcePrescribedLift_canonicalOrder F K s hs
      level hStrict n hCover x y
  · intro x
    calc
      h ((e x).1) = h (level x.val.1) := by
        rw [finiteSourcePrescribedLift_birthLevel F K s hs
          level hStrict n hCover x]
      _ = x.val.1 := chosenInverseLevel_spec h (hRange x.val x.property)
  · exact finiteSourcePrescribedLift_RHValues
      F K s hs level hStrict n hCover

end BigHrushovski.CFCoherentTower
