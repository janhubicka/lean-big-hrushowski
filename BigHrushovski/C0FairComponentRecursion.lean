import BigHrushovski.C0EnabledComponentExistence

/-!
# Track A: fair intrinsic-component prefixes in the countable C₀ limit

The next component is the equality class of the complete unary value
of the least *numerically labelled* enabled vertex. This is deliberately
different from selecting a smallest closure-rank at every stage.

The finite prefixes are defined by primitive recursion. A separate
fairness argument proves that every vertex eventually enters some prefix:
strict lower dependencies have smaller finite closure rank, while an
enabled component cannot be postponed forever because each intervening
selection consumes a distinct, no-larger numerical priority.

The graph-theoretic consequences use exact cofinal canonical C₀ stages;
the combinatorial exhaustion theorem needs only complete finite unary
values. No choice of a canonical order *inside* a component is made here.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The least numeric label outside Q whose strict lower complete
unary dependencies are all in Q. -/
noncomputable def leastEnabledVertex
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) : ℕ :=
  Nat.find (exists_enabledVertex C hC Q)

theorem leastEnabledVertex_spec
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) :
    leastEnabledVertex C hC Q ∉ Q ∧
      strictLowerValue C (leastEnabledVertex C hC Q) ⊆ Q :=
  Nat.find_spec (exists_enabledVertex C hC Q)

theorem leastEnabledVertex_le
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) (x : ℕ)
    (hx : x ∉ Q ∧ strictLowerValue C x ⊆ Q) :
    leastEnabledVertex C hC Q ≤ x :=
  Nat.find_min' (exists_enabledVertex C hC Q) hx

/-- Q₀=∅; Qₙ₊₁ adjoins one entire enabled intrinsic component to Qₙ. -/
noncomputable def fairComponentPrefix
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C) :
    ℕ → Finset ℕ :=
  Nat.rec ∅ (fun _ Q =>
    Q ∪ unaryComponent C (leastEnabledVertex C hC Q))

theorem fairComponentPrefix_zero
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C) :
    fairComponentPrefix C hC 0 = ∅ := rfl

theorem fairComponentPrefix_succ
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    fairComponentPrefix C hC (n + 1) =
      fairComponentPrefix C hC n ∪
        unaryComponent C
          (leastEnabledVertex C hC (fairComponentPrefix C hC n)) := rfl

theorem fairComponentPrefix_subset_succ
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    fairComponentPrefix C hC n ⊆ fairComponentPrefix C hC (n + 1) := by
  rw [fairComponentPrefix_succ]
  exact Finset.subset_union_left

theorem fairComponentPrefix_mono
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n m : ℕ) (hnm : n ≤ m) :
    fairComponentPrefix C hC n ⊆ fairComponentPrefix C hC m := by
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ m _ ih =>
      exact ih.trans (fairComponentPrefix_subset_succ C hC m)

/-- A stage really consumes a new component, so its finite prefix
strictly increases. -/
theorem fairComponentPrefix_ssubset_succ
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n : ℕ) :
    fairComponentPrefix C hC n ⊂ fairComponentPrefix C hC (n + 1) := by
  classical
  let Q := fairComponentPrefix C hC n
  let x := leastEnabledVertex C hC Q
  have hxNot : x ∉ Q := (leastEnabledVertex_spec C hC Q).1
  have hxP : x ∈ unaryComponent C x :=
    mem_unaryComponent_self C hC x
  have hxNew : x ∈ fairComponentPrefix C hC (n + 1) := by
    rw [fairComponentPrefix_succ]
    exact Finset.mem_union.mpr (Or.inr hxP)
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨fairComponentPrefix_subset_succ C hC n, ?_⟩
  intro heq
  have hxNotNew : x ∉ fairComponentPrefix C hC (n + 1) := by
    rw [← heq]
    exact hxNot
  exact hxNotNew hxNew

/-- Every new member of the (n+1)-st prefix belongs to exactly the
chosen intrinsic component, hence has its complete unary value.
No within-component numerical order is imposed. -/
theorem fairComponentPrefix_new_value
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (n x : ℕ)
    (hx : x ∈ fairComponentPrefix C hC (n + 1) \
      fairComponentPrefix C hC n) :
    C x = C (leastEnabledVertex C hC
      (fairComponentPrefix C hC n)) := by
  have hxNew : x ∈ fairComponentPrefix C hC (n + 1) :=
    (Finset.mem_sdiff.mp hx).1
  have hxOld : x ∉ fairComponentPrefix C hC n :=
    (Finset.mem_sdiff.mp hx).2
  rw [fairComponentPrefix_succ] at hxNew
  rcases Finset.mem_union.mp hxNew with hOld | hP
  · exact (hxOld hOld).elim
  · exact (mem_unaryComponent_iff C hC _ x).mp hP

/-- The number of labels at most x that have entered a prefix strictly
increases at every step as long as x itself is enabled and unlisted.
This avoids any assumption that closure ranks have finite sublevels. -/
private theorem fairComponentPrefix_smallLabels_grow
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x n : ℕ)
    (hLower : strictLowerValue C x ⊆ fairComponentPrefix C hC n)
    (hxNot : x ∉ fairComponentPrefix C hC n) :
    ((Finset.range (x + 1)) ∩ fairComponentPrefix C hC n).card <
      ((Finset.range (x + 1)) ∩
        fairComponentPrefix C hC (n + 1)).card := by
  classical
  let Q := fairComponentPrefix C hC n
  let y := leastEnabledVertex C hC Q
  have hyNot : y ∉ Q := (leastEnabledVertex_spec C hC Q).1
  have hyLe : y ≤ x :=
    leastEnabledVertex_le C hC Q x ⟨hxNot, hLower⟩
  have hyRange : y ∈ Finset.range (x + 1) :=
    Finset.mem_range.mpr (by omega)
  have hyNew : y ∈ fairComponentPrefix C hC (n + 1) := by
    rw [fairComponentPrefix_succ]
    exact Finset.mem_union.mpr
      (Or.inr (mem_unaryComponent_self C hC y))
  have hSub :
      (Finset.range (x + 1)) ∩ fairComponentPrefix C hC n ⊆
        (Finset.range (x + 1)) ∩ fairComponentPrefix C hC (n + 1) := by
    intro z hz
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hz).1,
        fairComponentPrefix_subset_succ C hC n
          (Finset.mem_inter.mp hz).2⟩
  have hNe :
      (Finset.range (x + 1)) ∩ fairComponentPrefix C hC n ≠
        (Finset.range (x + 1)) ∩ fairComponentPrefix C hC (n + 1) := by
    intro heq
    have hyRight :
        y ∈ (Finset.range (x + 1)) ∩
          fairComponentPrefix C hC (n + 1) :=
      Finset.mem_inter.mpr ⟨hyRange, hyNew⟩
    have hyLeft :
        y ∈ (Finset.range (x + 1)) ∩ fairComponentPrefix C hC n := by
      rw [heq]
      exact hyRight
    exact hyNot (Finset.mem_inter.mp hyLeft).2
  exact Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩)

/-- Once all strict lower dependencies of x are in one prefix,
the least-label policy must eventually list x. This is a finite
pigeonhole argument on labels 0,...,x, not on closure rank. -/
theorem fairComponentPrefix_eventually_of_lower
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x n : ℕ)
    (hLower : strictLowerValue C x ⊆ fairComponentPrefix C hC n) :
    ∃ m : ℕ, x ∈ fairComponentPrefix C hC m := by
  classical
  by_contra hNo
  push_neg at hNo
  have hNever (k : ℕ) :
      x ∉ fairComponentPrefix C hC (n + k) :=
    hNo (n + k)
  have hGrow : ∀ k : ℕ,
      k ≤ ((Finset.range (x + 1)) ∩
        fairComponentPrefix C hC (n + k)).card := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
        have hLowerK :
            strictLowerValue C x ⊆
              fairComponentPrefix C hC (n + k) :=
          hLower.trans
            (fairComponentPrefix_mono C hC n (n + k) (by omega))
        have hStep :=
          fairComponentPrefix_smallLabels_grow
            C hC x (n + k) hLowerK (hNever k)
        have hEq : n + k + 1 = n + (k + 1) := by omega
        rw [hEq] at hStep
        omega
  have hMany := hGrow (x + 1)
  have hProper :
      (Finset.range (x + 1)) ∩
        fairComponentPrefix C hC (n + (x + 1)) ⊂
      Finset.range (x + 1) := by
    refine Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hxRange : x ∈ Finset.range (x + 1) :=
      Finset.mem_range.mpr (by omega)
    have hxLeft :
        x ∈ (Finset.range (x + 1)) ∩
          fairComponentPrefix C hC (n + (x + 1)) := by
      rw [heq]
      exact hxRange
    exact hNever (x + 1) (Finset.mem_inter.mp hxLeft).2
  have hFew := Finset.card_lt_card hProper
  simp only [Finset.card_range] at hFew
  omega

/-- A finite family of vertices which are individually eventually
listed is included in one common prefix. -/
private theorem fairComponentPrefix_finite_coverage
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (s : Finset ℕ) :
    (∀ x ∈ s, ∃ n, x ∈ fairComponentPrefix C hC n) →
      ∃ n, s ⊆ fairComponentPrefix C hC n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, Finset.empty_subset _⟩
  | @insert x s hxs ih =>
      intro hs
      obtain ⟨nx, hx⟩ := hs x (Finset.mem_insert_self x s)
      have hs' : ∀ y ∈ s, ∃ n, y ∈ fairComponentPrefix C hC n := by
        intro y hy
        exact hs y (Finset.mem_insert_of_mem hy)
      obtain ⟨ns, hns⟩ := ih hs'
      refine ⟨max nx ns, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyS
      · exact (fairComponentPrefix_mono C hC nx (max nx ns)
          (Nat.le_max_left nx ns)) hx
      · exact (fairComponentPrefix_mono C hC ns (max nx ns)
          (Nat.le_max_right nx ns)) (hns hyS)

/-- The fair order-type-ω component schedule exhausts the entire
countable carrier. Each vertex has only finitely many lower
dependencies of smaller closure cardinality; once they are covered,
the least enabled label policy eventually selects its component. -/
theorem fairComponentPrefix_exhaustive
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (x : ℕ) :
    ∃ n : ℕ, x ∈ fairComponentPrefix C hC n := by
  have hRank : ∀ k : ℕ, ∀ y : ℕ,
      (C y).card = k →
        ∃ n, y ∈ fairComponentPrefix C hC n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro y hyk
        have hLowerEach : ∀ z ∈ strictLowerValue C y,
            ∃ n, z ∈ fairComponentPrefix C hC n := by
          intro z hz
          have hlt : (C z).card < k := by
            have h := strictLowerValue_card_lt C hC hz
            omega
          exact ih (C z).card hlt z rfl
        obtain ⟨n, hn⟩ :=
          fairComponentPrefix_finite_coverage
            C hC (strictLowerValue C y) hLowerEach
        exact fairComponentPrefix_eventually_of_lower C hC y n hn
  exact hRank (C x).card x rfl

/-- Under the exact finite canonical C₀ stage hypotheses, every
recursive prefix is closed under all complete unary values. -/
theorem canonicalStages_fairComponentPrefix_closed
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C) (n : ℕ) :
    N.IsClosedUnderValues C (fairComponentPrefix C hC n) := by
  induction n with
  | zero =>
      intro x hx
      simp [fairComponentPrefix_zero] at hx
  | succ n ih =>
      rw [fairComponentPrefix_succ]
      exact canonicalStages_enabledComponent_closed
        N C stage hCover hStage
        (fairComponentPrefix C hC n) ih
        (leastEnabledVertex C hC (fairComponentPrefix C hC n))
        (leastEnabledVertex_spec C hC (fairComponentPrefix C hC n)).2

/-- Each recursive increment is an actual minimal strong step in N,
and every new prefix is globally strong in N. -/
theorem canonicalStages_fairComponentPrefix_minimal_and_strong
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (hC : IsCompleteUnaryClosure C) (n : ℕ) :
    N.toPredimension.IsMinimalStrongStep
      (fairComponentPrefix C hC n)
      (fairComponentPrefix C hC (n + 1)) ∧
    N.toPredimension.IsGloballyStrong
      (fairComponentPrefix C hC (n + 1)) := by
  rw [fairComponentPrefix_succ]
  exact canonicalStages_enabledComponent_step_and_strong
    N C stage hCover hStage
    (fairComponentPrefix C hC n)
    (canonicalStages_fairComponentPrefix_closed
      N C stage hCover hStage hC n)
    (leastEnabledVertex C hC (fairComponentPrefix C hC n))
    (leastEnabledVertex_spec C hC (fairComponentPrefix C hC n)).1
    (leastEnabledVertex_spec C hC (fairComponentPrefix C hC n)).2

end FiniteC0
end BigHrushovski
