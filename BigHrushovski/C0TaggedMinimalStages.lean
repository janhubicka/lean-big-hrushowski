import BigHrushovski.C0TaggedStageCuts
import BigHrushovski.C0LocalFreeConverse

/-!
# Minimal strong stages in a tagged C₀ component-index join

This is the remaining graph-theoretic stage calculation needed for
finite two-sided functional amalgamation. All joined prefixes are
identified literally by C0TaggedStageCuts. Every right index level
either contains no fresh right-tail vertex (and hence contributes
nothing to the join) or adds precisely one right increment.

When a right-tail vertex appears, the frontloaded common base is
already in the old right prefix; there are no edges from this new
right block to the left private tail. The already proved no-cross
minimality lemma transports the original right step to the joined
prefix. The two component orders on the base need not agree.

The assertions here concern graph minimality of the stages only;
preservation of the complete unary functions is certified separately.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- Every base vertex precedes a right-tail component if the
right presentation is frontloaded. -/
theorem rightBase_oldStage_of_tail
    (κR : Sum P R → Fin m)
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (j : ℕ) (r : R) (hr : (κR (.inr r)).val = j) :
    (rightBase : Finset (Sum P R)) ⊆
      FiniteC0.oldStage κR j := by
  classical
  intro u hu
  obtain ⟨p, _, hEq⟩ := Finset.mem_image.mp hu
  rw [← hEq]
  apply (FiniteC0.mem_oldStage_iff κR j (.inl p)).mpr
  have h := hFront p r
  omega

/-- The entire component on a rank containing a right-tail
vertex consists of right-tail vertices, never base vertices. -/
theorem rightComponent_all_tail
    (κR : Sum P R → Fin m)
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (j : ℕ) (r : R) (hr : (κR (.inr r)).val = j)
    (u : Sum P R) (hu : u ∈ FiniteC0.component κR j) :
    ∃ r' : R, u = .inr r' := by
  cases u with
  | inl p =>
      have hp := (FiniteC0.mem_component_iff κR j (.inl p)).mp hu
      have hlt := hFront p r
      omega
  | inr r' =>
      exact ⟨r', rfl⟩

/-- If no right-tail vertex has rank j, the corresponding joined
step is empty, even if the right presentation processes base
components at j. -/
theorem joinedIndex_rightStep_eq_of_noTail
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (j : ℕ)
    (hNoTail : ¬ ∃ r : R, (κR (.inr r)).val = j) :
    FiniteC0.oldStage (joinedIndex κL κR) (n + j) =
      FiniteC0.oldStage (joinedIndex κL κR) (n + j + 1) := by
  classical
  ext x
  cases x with
  | inl p =>
      simp only [FiniteC0.mem_oldStage_iff]
      change (κL (.inl p)).val < n+j ↔
        (κL (.inl p)).val < n+j+1
      have hBound := (κL (.inl p)).isLt
      omega
  | inr z =>
      cases z with
      | inl l =>
          simp only [FiniteC0.mem_oldStage_iff]
          change (κL (.inr l)).val < n+j ↔
            (κL (.inr l)).val < n+j+1
          have hBound := (κL (.inr l)).isLt
          omega
      | inr r =>
          simp only [FiniteC0.mem_oldStage_iff]
          change n+(κR (.inr r)).val < n+j ↔
            n+(κR (.inr r)).val < n+j+1
          have hNe : (κR (.inr r)).val ≠ j := by
            intro heq
            exact hNoTail ⟨r, heq⟩
          omega

/-- A genuinely fresh right component is a minimal strong
increment over the entire corresponding joined prefix. This
uses only the original right minimal-step, actual tagged
inducedness and the no-cross calculation. -/
theorem joinedIndex_rightTail_minimalStep
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val)
    (j : ℕ) (r : R) (hr : (κR (.inr r)).val = j)
    (hMinimal : H.toPredimension.IsMinimalStrongStep
      (FiniteC0.oldStage κR j)
      (FiniteC0.oldStage κR (j+1))) :
    (freeGraph G H).toPredimension.IsMinimalStrongStep
      (FiniteC0.oldStage (joinedIndex κL κR) (n+j))
      (FiniteC0.oldStage (joinedIndex κL κR) (n+j+1)) := by
  classical
  let E := freeGraph G H
  let A : Finset (Carrier P L R) :=
    (leftDomain : Finset (Carrier P L R)) ∪
      (FiniteC0.oldStage κR j).image
        (rightTag : Sum P R → Carrier P L R)
  let Q : Finset (Carrier P L R) :=
    (FiniteC0.oldStage κR j).image
      (rightTag : Sum P R → Carrier P L R)
  let B : Finset (Carrier P L R) :=
    (FiniteC0.component κR j).image
      (rightTag : Sum P R → Carrier P L R)
  have hBase : (rightBase : Finset (Sum P R)) ⊆
      FiniteC0.oldStage κR j :=
    rightBase_oldStage_of_tail κR hFront j r hr
  have hTail : ∀ u : Sum P R, u ∈ FiniteC0.component κR j →
      ∃ r' : R, u = .inr r' :=
    rightComponent_all_tail κR hFront j r hr
  have hDisjointLeft : Disjoint
      (leftDomain : Finset (Carrier P L R)) B := by
    apply Finset.disjoint_left.mpr
    intro x hxLeft hxB
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hxLeft
    obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hxB
    obtain ⟨r', hUr⟩ := hTail u hu
    subst u
    have hBad : leftTag v = (rightTag (.inr r') : Carrier P L R) :=
      hv.trans hEq.symm
    cases v with
    | inl p => cases hBad
    | inr l => cases hBad
  have hDisjointRight : Disjoint Q B := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxB
    obtain ⟨v, hv, hV⟩ := Finset.mem_image.mp hxQ
    obtain ⟨u, hu, hU⟩ := Finset.mem_image.mp hxB
    have hvu : v = u := rightTag_injective (hV.trans hU.symm)
    subst u
    exact (Finset.disjoint_left.mp
      (FiniteC0.oldStage_disjoint_component κR j)) hv hu
  have hDisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    rcases Finset.mem_union.mp hxA with hxLeft | hxQ
    · exact (Finset.disjoint_left.mp hDisjointLeft) hxLeft hxB
    · exact (Finset.disjoint_left.mp hDisjointRight) hxQ hxB
  have hQsub : Q ⊆ A := Finset.subset_union_right
  have hBack : ∀ u ∈ B, ∀ v ∈ A, E.adj u v → v ∈ Q := by
    intro u hu v hv hAdj
    rcases Finset.mem_union.mp hv with hvLeft | hvQ
    · obtain ⟨uR, huR, huEq⟩ := Finset.mem_image.mp hu
      obtain ⟨r', hUr⟩ := hTail uR huR
      subst uR
      obtain ⟨vL, _, hvEq⟩ := Finset.mem_image.mp hvLeft
      cases vL with
      | inl p =>
          have hpBase : (Sum.inl p : Sum P R) ∈ rightBase :=
            Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
          have hpOld := hBase hpBase
          exact Finset.mem_image.mpr
            ⟨.inl p, hpOld,
              by simpa [leftTag, rightTag] using hvEq⟩
      | inr l =>
          have hAdj' : E.adj (rightTag (.inr r')) (leftTag (.inr l)) := by
            rw [huEq, hvEq]
            exact hAdj
          have hReverse : E.adj (leftTag (.inr l)) (rightTag (.inr r')) :=
            E.symm _ _ hAdj'
          exact ((freeGraph_no_cross G H l r') hReverse).elim
    · exact hvQ
  have hNo : E.NoCrossEdges A (Q ∪ B) :=
    E.noCross_of_backNeighbours A Q B hQsub hBack
  have hAdjRight : ∀ x y : Sum P R,
      H.adj x y ↔ E.adj (rightTag x) (rightTag y) :=
    fun x y => (freeGraph_right G H hAgree x y).symm
  have hSub : FiniteC0.oldStage κR j ⊆
      FiniteC0.oldStage κR (j+1) := by
    intro x hx
    apply (FiniteC0.mem_oldStage_iff κR (j+1) x).mpr
    have hlt := (FiniteC0.mem_oldStage_iff κR j x).mp hx
    omega
  have hLocal :
      E.toPredimension.IsMinimalStrongStep Q (Q ∪ B) := by
    have h := (H.minimalStrongStep_image_iff E
      (rightTag : Sum P R → Carrier P L R)
      rightTag_injective hAdjRight
      (FiniteC0.oldStage κR j)
      (FiniteC0.oldStage κR (j+1)) hSub).mpr hMinimal
    have hImage :
        (FiniteC0.oldStage κR (j+1)).image
          (rightTag : Sum P R → Carrier P L R) = Q ∪ B := by
      simp [FiniteC0.oldStage_succ, Q, B, Finset.image_union]
    change E.toPredimension.IsMinimalStrongStep Q
      ((FiniteC0.oldStage κR (j+1)).image
        (rightTag : Sum P R → Carrier P L R)) at h
    rw [hImage] at h
    exact h
  have hLift : E.toPredimension.IsMinimalStrongStep A (A ∪ B) :=
    E.minimalStrongStep_enlarged_of_local Q A B hQsub
      hDisj hNo hLocal
  have hImage :
      (FiniteC0.oldStage κR (j+1)).image
        (rightTag : Sum P R → Carrier P L R) = Q ∪ B := by
    simp [FiniteC0.oldStage_succ, Q, B, Finset.image_union]
  rw [show n+j+1 = n+(j+1) by omega,
    joinedIndex_oldStage_right κL κR j,
    joinedIndex_oldStage_right κL κR (j+1),
    hImage]
  change E.toPredimension.IsMinimalStrongStep A
    ((leftDomain : Finset (Carrier P L R)) ∪ (Q ∪ B))
  simpa only [A, Finset.union_assoc] using hLift

/-- All joined stages are empty or minimal strong. The left
presentation is retained exactly; the right base may have a
different order, and its right-tail increments are appended. -/
theorem joinedIndex_minimalStages
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (hLeft : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κL k =
        FiniteC0.oldStage κL (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κL k)
        (FiniteC0.oldStage κL (k+1)))
    (hRight : ∀ j : ℕ, j < m →
      FiniteC0.oldStage κR j =
        FiniteC0.oldStage κR (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κR j)
        (FiniteC0.oldStage κR (j+1)))
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val) :
    ∀ k : ℕ, k < n+m →
      FiniteC0.oldStage (joinedIndex κL κR) k =
        FiniteC0.oldStage (joinedIndex κL κR) (k+1) ∨
      (freeGraph G H).toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage (joinedIndex κL κR) k)
        (FiniteC0.oldStage (joinedIndex κL κR) (k+1)) := by
  classical
  intro k hk
  by_cases hkLeft : k < n
  · rcases hLeft k hkLeft with hEq | hMin
    · left
      rw [joinedIndex_oldStage_left κL κR k (by omega),
        joinedIndex_oldStage_left κL κR (k+1) (by omega), hEq]
    · right
      have hAdjLeft : ∀ x y : Sum P L,
          G.adj x y ↔ (freeGraph G H).adj (leftTag x) (leftTag y) :=
        fun x y => (freeGraph_left G H hAgree x y).symm
      have hSub : FiniteC0.oldStage κL k ⊆
          FiniteC0.oldStage κL (k+1) := by
        intro x hx
        apply (FiniteC0.mem_oldStage_iff κL (k+1) x).mpr
        have hlt := (FiniteC0.mem_oldStage_iff κL k x).mp hx
        omega
      have hImage := (G.minimalStrongStep_image_iff
          (freeGraph G H)
          (leftTag : Sum P L → Carrier P L R)
          leftTag_injective hAdjLeft
          (FiniteC0.oldStage κL k)
          (FiniteC0.oldStage κL (k+1)) hSub).mpr hMin
      rw [joinedIndex_oldStage_left κL κR k (by omega),
        joinedIndex_oldStage_left κL κR (k+1) (by omega)]
      exact hImage
  · let j := k-n
    have hj : j < m := by dsimp [j]; omega
    have hk' : k = n+j := by dsimp [j]; omega
    rcases hRight j hj with hEq | hMin
    · left
      rw [hk',
        show n+j+1 = n+(j+1) by omega,
        joinedIndex_oldStage_right κL κR j,
        joinedIndex_oldStage_right κL κR (j+1), hEq]
    · by_cases hTail : ∃ r : R, (κR (.inr r)).val = j
      · right
        obtain ⟨r, hr⟩ := hTail
        rw [hk']
        exact joinedIndex_rightTail_minimalStep
          G H hAgree κL κR hFront j r hr hMin
      · left
        rw [hk']
        exact joinedIndex_rightStep_eq_of_noTail κL κR j hTail

end TaggedAmalgam
end BigHrushovski
