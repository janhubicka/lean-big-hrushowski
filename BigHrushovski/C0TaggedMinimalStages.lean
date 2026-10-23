import BigHrushovski.C0TaggedSharedBaseValues
import BigHrushovski.C0TaggedMinimal

/-!
# Exact finite stages of the left-order-fixed tagged C0 component index

A joined index preserves the complete old left component order and
places all new right components after it. The first n joined stages
are EXACTLY the images of the old left stages. Each later joined
stage is the whole left factor together with the first j right-tail
components, and each later component is precisely one right-tail
component.

These equalities are the combinatorial bridge between the already
verified two-sided full unary-value theorem and the no-cross
minimal-strong extension transfer of C0LocalFreeConverse.

The canonical index may have empty stages. Those are harmless in the
finite C0 presentation; nonempty stages must be minimal strong steps.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

noncomputable def rightTailPrefix
    (κR : Sum P R → Fin m) (j : ℕ) :
    Finset (Carrier P L R) := by
  classical
  exact ((Finset.univ : Finset R).filter
    (fun r => (κR (.inr r)).val < j)).image
      (fun r => rightTag (Sum.inr r))

theorem rightTailPrefix_mem_iff
    (κR : Sum P R → Fin m) (j : ℕ) (r : R) :
    (rightTag (Sum.inr r) : Carrier P L R) ∈
      rightTailPrefix κR j ↔ (κR (.inr r)).val < j := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs, heq⟩ :=
      Finset.mem_image.mp (show
        rightTag (Sum.inr r) ∈ rightTailPrefix κR j from h)
    have heq' : (Sum.inr s : Sum P R) = .inr r :=
      rightTag_injective heq
    have hsr : s = r := Sum.inr.inj heq'
    subst s
    exact (Finset.mem_filter.mp hs).2
  · intro hr
    exact Finset.mem_image.mpr
      ⟨r, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hr⟩, rfl⟩

private theorem rightTail_not_leftDomain (r : R) :
    (rightTag (Sum.inr r) : Carrier P L R) ∉
      (leftDomain : Finset (Carrier P L R)) := by
  intro h
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
  cases u with
  | inl p =>
      simp [rightTag, leftTag] at hu
  | inr l =>
      simp [rightTag, leftTag] at hu

/-- Each old left stage stays literally the same set of vertices
in the joined graph; no new right vertex appears before rank n. -/
theorem joinedIndex_oldStage_before
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (k : ℕ) (hk : k ≤ n) :
    FiniteC0.oldStage (joinedIndex κL κR) k =
      (FiniteC0.oldStage κL k).image
        (leftTag : Sum P L → Carrier P L R) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hlt :
        (joinedIndex κL κR x).val < k :=
      (FiniteC0.mem_oldStage_iff (joinedIndex κL κR) k x).mp hx
    cases x with
    | inl p =>
        exact Finset.mem_image.mpr
          ⟨.inl p, (FiniteC0.mem_oldStage_iff κL k (.inl p)).mpr
            (by exact hlt), rfl⟩
    | inr side =>
        cases side with
        | inl l =>
            exact Finset.mem_image.mpr
              ⟨.inr l, (FiniteC0.mem_oldStage_iff κL k (.inr l)).mpr
                (by exact hlt), rfl⟩
        | inr r =>
            have hv : n + (κR (.inr r)).val < k := hlt
            omega
  · intro hx
    obtain ⟨u, hu, huEq⟩ := Finset.mem_image.mp hx
    rw [← huEq]
    apply (FiniteC0.mem_oldStage_iff
      (joinedIndex κL κR) k (leftTag u)).mpr
    rw [joinedIndex_left_val]
    exact (FiniteC0.mem_oldStage_iff κL k u).mp hu

/-- After the left factor has been fully enumerated, the next
j stages are its entire image plus precisely the right-tail
components that occurred before rank j in the right factor. -/
theorem joinedIndex_oldStage_after
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (j : ℕ) :
    FiniteC0.oldStage (joinedIndex κL κR) (n+j) =
      (leftDomain : Finset (Carrier P L R)) ∪
      rightTailPrefix κR j := by
  classical
  apply Finset.ext
  intro x
  cases x with
  | inl p =>
      have hxLeft : (Sum.inl p : Carrier P L R) ∈
          (leftDomain : Finset (Carrier P L R)) :=
        leftTag_mem_domain (.inl p)
      have hRank := (κL (.inl p)).isLt
      constructor
      · intro _
        exact Finset.mem_union.mpr (Or.inl hxLeft)
      · intro _
        exact (FiniteC0.mem_oldStage_iff
          (joinedIndex κL κR) (n+j) (.inl p)).mpr
          (by change (κL (.inl p)).val < n+j; omega)
  | inr side =>
      cases side with
      | inl l =>
          have hxLeft : (Sum.inr (Sum.inl l) : Carrier P L R) ∈
              (leftDomain : Finset (Carrier P L R)) :=
            leftTag_mem_domain (.inr l)
          have hRank := (κL (.inr l)).isLt
          constructor
          · intro _
            exact Finset.mem_union.mpr (Or.inl hxLeft)
          · intro _
            exact (FiniteC0.mem_oldStage_iff
              (joinedIndex κL κR) (n+j) (.inr (.inl l))).mpr
              (by change (κL (.inr l)).val < n+j; omega)
      | inr r =>
          have hNotLeft := rightTail_not_leftDomain (P := P) (L := L) r
          constructor
          · intro hx
            have hRank := (FiniteC0.mem_oldStage_iff
              (joinedIndex κL κR) (n+j)
                (rightTag (.inr r))).mp hx
            have hr : (κR (.inr r)).val < j := by
              change n + (κR (.inr r)).val < n+j at hRank
              omega
            exact Finset.mem_union.mpr
              (Or.inr ((rightTailPrefix_mem_iff κR j r).mpr hr))
          · intro hx
            rcases Finset.mem_union.mp hx with hLeft | hRight
            · exact False.elim (hNotLeft hLeft)
            · have hr := (rightTailPrefix_mem_iff κR j r).mp hRight
              exact (FiniteC0.mem_oldStage_iff
                (joinedIndex κL κR) (n+j)
                  (rightTag (.inr r))).mpr (by
                    change n + (κR (.inr r)).val < n+j
                    omega)

/-- At rank n the joined old stage is the entire left graph. -/
theorem joinedIndex_oldStage_boundary
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m) :
    FiniteC0.oldStage (joinedIndex κL κR) n =
      (leftDomain : Finset (Carrier P L R)) := by
  have hZero : rightTailPrefix κR 0 = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨r, hr, hEq⟩ := Finset.mem_image.mp hx
    have hlt := (Finset.mem_filter.mp hr).2
    omega
  have hAfter := joinedIndex_oldStage_after κL κR 0
  simpa [hZero] using hAfter

end TaggedAmalgam
end BigHrushovski
