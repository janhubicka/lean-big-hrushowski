import BigHrushovski.CountableCover

/-!
# From finite strong steps to globally strong finite stages

A strong Fraisse construction is often specified as a countable chain of
finite induced substructures, each strong in its successor. We show that
these local strong-step assumptions and coverage suffice for every stage
to be strong in the whole ambient structure.

The ambient predimension is a function on finite subsets of an arbitrary
possibly infinite vertex type; no graph construction or homogeneity is
assumed here.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

/-- Increasing finite stages with strong successor inclusions which cover
every vertex. The monotonicity follows from the strong-step assumption. -/
structure StrongChain (d : Predimension V) where
  stage : ℕ → Finset V
  strong_step : ∀ n : ℕ, d.IsStrong (stage n) (stage (n + 1))
  covers : ∀ v : V, ∃ n : ℕ, v ∈ stage n

namespace StrongChain

variable (e : StrongChain d)

/-- Every earlier stage is strong in every later stage. -/
theorem strong_stages {n m : ℕ} (hnm : n ≤ m) :
    d.IsStrong (e.stage n) (e.stage m) := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact d.strong_refl _
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact d.strong_trans (ih hle) (e.strong_step m)
      · have heq : n = m + 1 := by omega
        subst n
        exact d.strong_refl _

/-- Monotonicity is a consequence, not an additional assumption. -/
theorem stage_monotone {n m : ℕ} (hnm : n ≤ m) :
    e.stage n ⊆ e.stage m :=
  (e.strong_stages hnm).1

/-- Every finite vertex set occurs in some stage. -/
theorem contains_finite (s : Finset V) :
    ∃ n : ℕ, s ⊆ e.stage n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, Finset.empty_subset _⟩
  | @insert v s hnot ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨j, hj⟩ := e.covers v
      refine ⟨max i j, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hws
      · exact (e.stage_monotone (Nat.le_max_right i j)) hj
      · exact (e.stage_monotone (Nat.le_max_left i j)) (hi hws)

/-- Every finite stage is strong in the entire, possibly infinite
ambient structure. This is the crucial finite-to-countable step. -/
theorem stage_global (n : ℕ) :
    d.IsGloballyStrong (e.stage n) := by
  intro b hnb
  obtain ⟨m, hm⟩ := e.contains_finite (e.stage n ∪ b)
  have hnm : n ≤ max n m := Nat.le_max_left n m
  have hstrong : d.IsStrong (e.stage n) (e.stage (max n m)) :=
    e.strong_stages hnm
  have hb : b ⊆ e.stage (max n m) := by
    intro v hv
    exact (e.stage_monotone (Nat.le_max_right n m))
      (hm (Finset.mem_union.mpr (Or.inr hv)))
  exact d.strong_restrict hstrong hnb hb

/-- Convert locally strong successor steps into a full strong exhaustion. -/
def toStrongExhaustion : StrongExhaustion d where
  stage := e.stage
  monotone := fun n m hnm => e.stage_monotone hnm
  strong := e.stage_global
  covers := e.covers

/-- A local strong chain already witnesses the finite strong-cover
property: every finite set lies in a finite globally strong stage. -/
theorem toFiniteStrongCover : FiniteStrongCover d :=
  StrongExhaustion.toFiniteStrongCover (e.toStrongExhaustion)

end StrongChain

namespace StrongExhaustion

variable (e : StrongExhaustion d)

/-- A strong exhaustion automatically has strong successor inclusions. -/
def toStrongChain : StrongChain d where
  stage := e.stage
  strong_step := by
    intro n
    exact e.strong n (e.stage (n + 1))
      (e.monotone n (n + 1) (Nat.le_succ n))
  covers := e.covers

end StrongExhaustion

/-- A covering chain of finite strong successor extensions and a strong
exhaustion carry exactly the same existence information. -/
theorem exists_strong_chain_iff_exhaustion :
    Nonempty (StrongChain d) ↔ Nonempty (StrongExhaustion d) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toStrongExhaustion⟩
  · rintro ⟨e⟩
    exact ⟨e.toStrongChain⟩

end Predimension
end BigHrushovski
