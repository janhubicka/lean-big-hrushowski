import BigHrushovski.C0FairComponentRecursion

/-!
# Track A: unique birth stages for the fair intrinsic components

Every vertex has a unique fair-component birth stage. The new vertices
at that stage form exactly one complete-unary equality class; its
strict lower closure was already present. The whole unary value is
therefore contained in the new prefix.

The proof uses only complete finite-valued unary closure for these
statements. Its use for predimension comes through the previously
certified canonical-stage fair recursion; choosing the required
within-component ordered representative remains a separate problem.
-/

namespace BigHrushovski
namespace FiniteC0

/-- All finite prefixes of the fair recursion are closed under C.
This purely unary statement does not require a graph or canonical
stage certificates. -/
theorem fairComponentPrefix_unaryClosed
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    ∀ y ∈ fairComponentPrefix C hC n,
      C y ⊆ fairComponentPrefix C hC n := by
  induction n with
  | zero =>
      intro y hy
      simp [fairComponentPrefix_zero] at hy
  | succ n ih =>
      rw [fairComponentPrefix_succ]
      intro y hy z hz
      let Q := fairComponentPrefix C hC n
      let x := leastEnabledVertex C hC Q
      rcases Finset.mem_union.mp hy with hyOld | hyP
      · exact Finset.mem_union.mpr (Or.inl (ih y hyOld hz))
      · have hCy : C y = C x :=
          (mem_unaryComponent_iff C hC x y).mp hyP
        have hzCx : z ∈ C x := by
          rw [← hCy]
          exact hz
        by_cases hzP : z ∈ unaryComponent C x
        · exact Finset.mem_union.mpr (Or.inr hzP)
        · have hzLower : z ∈ strictLowerValue C x :=
            Finset.mem_sdiff.mpr ⟨hzCx, hzP⟩
          exact Finset.mem_union.mpr
            (Or.inl ((leastEnabledVertex_spec C hC Q).2 hzLower))

/-- The component selected at one step is entirely new. In
particular, it cannot intersect an earlier closed prefix without
its chosen vertex already belonging to that prefix. -/
theorem fairComponentPrefix_fresh_component
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    fairComponentPrefix C hC (n + 1) \
        fairComponentPrefix C hC n =
      unaryComponent C
        (leastEnabledVertex C hC (fairComponentPrefix C hC n)) := by
  classical
  let Q := fairComponentPrefix C hC n
  let x := leastEnabledVertex C hC Q
  have hxNot : x ∉ Q := (leastEnabledVertex_spec C hC Q).1
  have hDisj : Disjoint Q (unaryComponent C x) := by
    apply Finset.disjoint_left.mpr
    intro y hyQ hyP
    have hCy : C y = C x :=
      (mem_unaryComponent_iff C hC x y).mp hyP
    have hxCy : x ∈ C y := by
      rw [hCy]
      exact hC.1 x
    exact hxNot
      ((fairComponentPrefix_unaryClosed C hC n) y hyQ hxCy)
  rw [fairComponentPrefix_succ]
  ext y
  constructor
  · intro hy
    have hyNew := (Finset.mem_sdiff.mp hy).1
    have hyNot := (Finset.mem_sdiff.mp hy).2
    rcases Finset.mem_union.mp hyNew with hyOld | hyP
    · exact (hyNot hyOld).elim
    · exact hyP
  · intro hyP
    refine Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inr hyP), ?_⟩
    intro hyQ
    exact (Finset.disjoint_left.mp hDisj) hyQ hyP

/-- Every vertex enters a finite fair prefix for the first time at
some uniquely determined component birth stage. -/
theorem fairComponentPrefix_exists_birth
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x : ℕ) :
    ∃ n : ℕ, x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n := by
  classical
  let p : ℕ → Prop := fun m => x ∈ fairComponentPrefix C hC m
  have hp : ∃ m, p m :=
    fairComponentPrefix_exhaustive C hC x
  have hFirst : p (Nat.find hp) :=
    Nat.find_spec hp
  have hZero : ¬ p 0 := by
    simp [p, fairComponentPrefix_zero]
  cases hIndex : Nat.find hp with
  | zero =>
      have hAtZero : p 0 := by
        simpa [hIndex] using hFirst
      exact (hZero hAtZero).elim
  | succ n =>
      have hxNew : x ∈ fairComponentPrefix C hC (n + 1) := by
        simpa [p, hIndex] using hFirst
      have hxOld : x ∉ fairComponentPrefix C hC n := by
        intro hy
        have hlt : n < Nat.find hp := by
          rw [hIndex]
          omega
        exact (Nat.find_min hp hlt) hy
      exact ⟨n, Finset.mem_sdiff.mpr ⟨hxNew, hxOld⟩⟩

/-- A vertex cannot have two distinct birth stages because the
prefixes are nested. -/
theorem fairComponentPrefix_birth_unique
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x n m : ℕ)
    (hn : x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n)
    (hm : x ∈ fairComponentPrefix C hC (m + 1) \
      fairComponentPrefix C hC m) :
    n = m := by
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hxM : x ∈ fairComponentPrefix C hC m :=
      (fairComponentPrefix_mono C hC (n + 1) m (by omega))
        (Finset.mem_sdiff.mp hn).1
    exact ((Finset.mem_sdiff.mp hm).2 hxM).elim
  · exact heq
  · have hxN : x ∈ fairComponentPrefix C hC n :=
      (fairComponentPrefix_mono C hC (m + 1) n (by omega))
        (Finset.mem_sdiff.mp hm).1
    exact ((Finset.mem_sdiff.mp hn).2 hxN).elim

theorem fairComponentPrefix_existsUnique_birth
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x : ℕ) :
    ∃! n : ℕ, x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n := by
  obtain ⟨n, hn⟩ := fairComponentPrefix_exists_birth C hC x
  exact ⟨n, hn, fun m hm =>
    fairComponentPrefix_birth_unique C hC x m n hm hn⟩

/-- When a vertex is born, every strict lower complete-unary
dependency was already present before the new component. -/
theorem fairComponentPrefix_new_lower_old
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n x : ℕ)
    (hx : x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n) :
    strictLowerValue C x ⊆ fairComponentPrefix C hC n := by
  have hValue :
      C x = C (leastEnabledVertex C hC
        (fairComponentPrefix C hC n)) :=
    fairComponentPrefix_new_value C hC n x hx
  have hLower :=
    (leastEnabledVertex_spec C hC
      (fairComponentPrefix C hC n)).2
  simpa [strictLowerValue, unaryComponent, hValue] using hLower

/-- The entire complete unary value of a vertex, not just its direct
graph predecessors, is already contained in the prefix at its birth. -/
theorem fairComponentPrefix_new_full_in_step
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n x : ℕ)
    (hx : x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n) :
    C x ⊆ fairComponentPrefix C hC (n + 1) :=
  fairComponentPrefix_unaryClosed C hC (n + 1) x
    (Finset.mem_sdiff.mp hx).1

end FiniteC0
end BigHrushovski
