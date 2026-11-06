import BigHrushovski.C0TaggedFunctionalOneBlock

/-!
# Exact finite stages of the joined C₀ component presentation

The joined index keeps all left component ranks unchanged and appends
only right-tail ranks, using the original right index after the base
has been frontloaded. This file identifies its literal finite stages.
No compatibility of the chronological orders on the common base is
required, and no abstract order-isomorphism replaces a tagged vertex.

These set equalities are prerequisites for iterating the one-block
two-sided functional amalgamation across the whole right tail.
They do not alone establish that every joined stage is minimal strong.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- Before the left endpoint, the joined presentation is exactly
the image of the original left prefix, including empty ranks. -/
theorem joinedIndex_oldStage_left
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (k : ℕ) (hk : k ≤ n) :
    FiniteC0.oldStage (joinedIndex κL κR) k =
      (FiniteC0.oldStage κL k).image
        (leftTag : Sum P L → Carrier P L R) := by
  classical
  ext x
  constructor
  · intro hx
    have hlt : (joinedIndex κL κR x).val < k :=
      (FiniteC0.mem_oldStage_iff (joinedIndex κL κR) k x).mp hx
    cases x with
    | inl p =>
        apply Finset.mem_image.mpr
        refine ⟨.inl p, ?_, rfl⟩
        exact (FiniteC0.mem_oldStage_iff κL k (.inl p)).mpr (by
          change (κL (.inl p)).val < k at hlt
          exact hlt)
    | inr z =>
        cases z with
        | inl l =>
            apply Finset.mem_image.mpr
            refine ⟨.inr l, ?_, rfl⟩
            exact (FiniteC0.mem_oldStage_iff κL k (.inr l)).mpr (by
              change (κL (.inr l)).val < k at hlt
              exact hlt)
        | inr r =>
            change n + (κR (.inr r)).val < k at hlt
            omega
  · intro hx
    obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hx
    rw [← hEq]
    apply (FiniteC0.mem_oldStage_iff
      (joinedIndex κL κR) k (leftTag u)).mpr
    rw [joinedIndex_left_val]
    exact (FiniteC0.mem_oldStage_iff κL k u).mp hu

/-- At its left endpoint the joined index contains exactly
the old factor; no right-tail vertex has entered. -/
theorem joinedIndex_oldStage_leftDomain
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m) :
    FiniteC0.oldStage (joinedIndex κL κR) n =
      (leftDomain : Finset (Carrier P L R)) := by
  rw [joinedIndex_oldStage_left κL κR n (le_refl n),
    FiniteC0.oldStage_final κL]
  rfl

/-- Each subsequent prefix consists of the entire original left
factor and the literal image of the corresponding right prefix.
The right-prefix image may contain old base vertices already on
the left, but this union introduces no duplicate vertices. -/
theorem joinedIndex_oldStage_right
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (j : ℕ) :
    FiniteC0.oldStage (joinedIndex κL κR) (n + j) =
      (leftDomain : Finset (Carrier P L R)) ∪
        (FiniteC0.oldStage κR j).image
          (rightTag : Sum P R → Carrier P L R) := by
  classical
  ext x
  constructor
  · intro hx
    cases x with
    | inl p =>
        exact Finset.mem_union.mpr
          (Or.inl (leftTag_mem_domain (P := P) (L := L) (R := R) (.inl p)))
    | inr z =>
        cases z with
        | inl l =>
            exact Finset.mem_union.mpr
              (Or.inl (leftTag_mem_domain (P := P) (L := L) (R := R) (.inr l)))
        | inr r =>
            have hlt : (joinedIndex κL κR
                (Sum.inr (Sum.inr r))).val < n + j :=
              (FiniteC0.mem_oldStage_iff
                (joinedIndex κL κR) (n + j) _).mp hx
            have hr : (κR (.inr r)).val < j := by
              change n + (κR (.inr r)).val < n + j at hlt
              omega
            apply Finset.mem_union.mpr
            apply Or.inr
            apply Finset.mem_image.mpr
            exact ⟨.inr r,
              (FiniteC0.mem_oldStage_iff κR j (.inr r)).mpr hr, rfl⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hLeft | hRight
    · obtain ⟨u, _, hEq⟩ := Finset.mem_image.mp hLeft
      rw [← hEq]
      apply (FiniteC0.mem_oldStage_iff
        (joinedIndex κL κR) (n + j) (leftTag u)).mpr
      rw [joinedIndex_left_val]
      have hBound := (κL u).isLt
      omega
    · obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp hRight
      rw [← hEq]
      cases u with
      | inl p =>
          apply (FiniteC0.mem_oldStage_iff
            (joinedIndex κL κR) (n + j) (rightTag (.inl p))).mpr
          rw [joinedIndex_right_base_val]
          have hBound := (κL (.inl p)).isLt
          omega
      | inr r =>
          apply (FiniteC0.mem_oldStage_iff
            (joinedIndex κL κR) (n + j) (rightTag (.inr r))).mpr
          rw [joinedIndex_right_tail_val]
          have hr := (FiniteC0.mem_oldStage_iff κR j (.inr r)).mp hu
          omega

/-- The exact right step is the left domain together with the
two consecutive original right prefixes. No claim of minimality
is built into this arithmetic identification. -/
theorem joinedIndex_rightStep
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (j : ℕ) :
    (FiniteC0.oldStage (joinedIndex κL κR) (n + j),
      FiniteC0.oldStage (joinedIndex κL κR) (n + j + 1)) =
    ((leftDomain : Finset (Carrier P L R)) ∪
        (FiniteC0.oldStage κR j).image
          (rightTag : Sum P R → Carrier P L R),
     (leftDomain : Finset (Carrier P L R)) ∪
        (FiniteC0.oldStage κR (j + 1)).image
          (rightTag : Sum P R → Carrier P L R)) := by
  rw [joinedIndex_oldStage_right κL κR j,
    show n + j + 1 = n + (j + 1) by omega,
    joinedIndex_oldStage_right κL κR (j + 1)]

end TaggedAmalgam
end BigHrushovski
