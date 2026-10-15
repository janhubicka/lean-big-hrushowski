import BigHrushovski.StrongChain
import BigHrushovski.CFDClosedDecomposition

/-!
# Countable chains of finite strictly d-closed extensions

Finite d-closed extensions are stricter than self-sufficient ones.
We prove directly that a covering sequence of finite stages with
successive strict d-closed inclusions makes every stage strictly
d-closed in the entire ambient graph.

This is reusable for the C_F construction and elsewhere. It
does not require growth bounds, a graph-genericity assumption,
a Ramsey theorem, or an encoding of the stage construction.

The conversion to an ordinary strong chain permits reuse of
the earlier countable cover results where strictness is not needed.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- Strict d-closedness in a possibly infinite ambient carrier,
tested on every finite proper extension of a finite base. -/
def IsGloballyDClosed (a : Finset V) : Prop :=
  ∀ b : Finset V, a ⊆ b → b ≠ a → d.delta a < d.delta b

/-- Restrict global strict d-closedness to any finite
ambient substructure containing the base. -/
theorem IsGloballyDClosed.restrict
    {a b : Finset V} (ha : d.IsGloballyDClosed a)
    (hab : a ⊆ b) : d.IsDClosed a b := by
  refine ⟨hab, ?_⟩
  intro c hac hne hcb
  exact ha c hac hne

/-- Strict closure inside a globally strictly closed structure
implies global strict closure of the smaller base. -/
theorem globallyDClosed_of_dClosed_in_global
    {a b : Finset V}
    (hab : d.IsDClosed a b)
    (hb : d.IsGloballyDClosed b) :
    d.IsGloballyDClosed a := by
  intro c hac hne
  have hbUnion : d.IsDClosed b (b ∪ c) :=
    hb.restrict Finset.subset_union_left
  have haUnion : d.IsDClosed a (b ∪ c) :=
    d.dclosed_trans hab hbUnion
  exact haUnion.2 c hac hne Finset.subset_union_right

/-- Finite stages with strict d-closed successor inclusions
which together cover the whole ambient carrier. -/
structure DClosedChain (d : Predimension V) where
  stage : ℕ → Finset V
  dclosed_step : ∀ n, d.IsDClosed (stage n) (stage (n + 1))
  covers : ∀ v : V, ∃ n, v ∈ stage n

namespace DClosedChain

variable {d : Predimension V} (e : DClosedChain d)

/-- Every earlier stage is strictly d-closed in every later stage. -/
theorem dclosed_stages {n m : ℕ} (hnm : n ≤ m) :
    d.IsDClosed (e.stage n) (e.stage m) := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact d.dclosed_refl _
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact d.dclosed_trans (ih hle) (e.dclosed_step m)
      · have heq : n = m + 1 := by omega
        subst n
        exact d.dclosed_refl _

theorem stage_monotone {n m : ℕ} (hnm : n ≤ m) :
    e.stage n ⊆ e.stage m :=
  (e.dclosed_stages hnm).1

/-- Every finite set of vertices is contained in a finite stage. -/
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

/-- Every finite stage is strictly d-closed in the *whole*
(possibly infinite) ambient carrier. -/
theorem stage_global (n : ℕ) :
    d.IsGloballyDClosed (e.stage n) := by
  intro b hnb hne
  obtain ⟨m, hm⟩ := e.contains_finite (e.stage n ∪ b)
  have hclosed : d.IsDClosed
      (e.stage n) (e.stage (max n m)) :=
    e.dclosed_stages (Nat.le_max_left n m)
  have hb : b ⊆ e.stage (max n m) := by
    intro v hv
    exact (e.stage_monotone (Nat.le_max_right n m))
      (hm (Finset.mem_union.mpr (Or.inr hv)))
  exact hclosed.2 b hnb hne hb

/-- Forgetting strictness recovers the established strong-chain
interface and all its finite-cover consequences. -/
def toStrongChain : StrongChain d where
  stage := e.stage
  strong_step := fun n => d.strong_of_dClosed (e.dclosed_step n)
  covers := e.covers

end DClosedChain
end Predimension
end BigHrushovski
