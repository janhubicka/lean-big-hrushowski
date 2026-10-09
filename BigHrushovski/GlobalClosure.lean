import BigHrushovski.Closure

/-!
# Globally strong finite sets and finite strong exhaustions

The ambient vertex type may be infinite. Predimension and self-sufficiency
are still evaluated only on finite vertex sets. A strong exhaustion is
supplied as explicit data; the existence of such an exhaustion for the
Hrushovski Fraisse limit is a separate theorem of the construction.

This module verifies that finite strong hulls do not depend on the finite
strong container, and constructs the least globally strong closure from
a strong exhaustion. No additional axioms are introduced.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- Finite strong substructure in an ambient (possibly infinite) vertex type. -/
def IsGloballyStrong (a : Finset V) : Prop :=
  ∀ b : Finset V, a ⊆ b → d.IsStrong a b

/-- Global strong substructures are closed under finite intersections. -/
theorem globallyStrong_inter {p q : Finset V}
    (hp : d.IsGloballyStrong p) (hq : d.IsGloballyStrong q) :
    d.IsGloballyStrong (p ∩ q) := by
  intro c hpc
  have hpu : d.IsStrong p (p ∪ q ∪ c) :=
    hp _ (Finset.subset_union_left.trans Finset.subset_union_left)
  have hqu : d.IsStrong q (p ∪ q ∪ c) :=
    hq _ (Finset.subset_union_right.trans Finset.subset_union_left)
  have hIu := d.strong_inter hpu hqu
  exact d.strong_restrict hIu hpc Finset.subset_union_right

/-- The strong hull in a globally strong container is itself globally strong. -/
theorem strongHull_global {a c : Finset V}
    (hc : d.IsGloballyStrong c) :
    d.IsGloballyStrong (d.strongHull a c) := by
  intro b hhb
  have hcu : d.IsStrong c (c ∪ b) :=
    hc _ Finset.subset_union_left
  have hhu : d.IsStrong (d.strongHull a c) (c ∪ b) :=
    d.strong_trans (d.strongHull_strong a c) hcu
  exact d.strong_restrict hhu hhb Finset.subset_union_right

/-- The finite hull in a globally strong container is contained in every
globally strong set containing its generators. -/
theorem strongHull_least_global {a b c : Finset V}
    (hc : d.IsGloballyStrong c) (hac : a ⊆ c)
    (hb : d.IsGloballyStrong b) (hab : a ⊆ b) :
    d.strongHull a c ⊆ b := by
  have hci : d.IsStrong (c ∩ b) c :=
    (d.globallyStrong_inter hc hb) c Finset.inter_subset_left
  have hai : a ⊆ c ∩ b := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hac hv, hab hv⟩
  exact (d.strongHull_least hai hci).trans Finset.inter_subset_right

/-- Independence of the finite globally strong container. -/
theorem strongHull_eq_of_global {a c c' : Finset V}
    (hc : d.IsGloballyStrong c) (hc' : d.IsGloballyStrong c')
    (hac : a ⊆ c) (hac' : a ⊆ c') :
    d.strongHull a c = d.strongHull a c' := by
  apply le_antisymm
  · exact d.strongHull_least_global hc hac
      (d.strongHull_global hc') (d.subset_strongHull hac')
  · exact d.strongHull_least_global hc' hac'
      (d.strongHull_global hc) (d.subset_strongHull hac)


/-- A set strong inside a finite globally strong container is globally strong. -/
theorem globallyStrong_of_strong_in_global {a b : Finset V}
    (hab : d.IsStrong a b) (hb : d.IsGloballyStrong b) :
    d.IsGloballyStrong a := by
  intro c hac
  have hbu : d.IsStrong b (b ∪ c) :=
    hb _ Finset.subset_union_left
  have hau : d.IsStrong a (b ∪ c) := d.strong_trans hab hbu
  exact d.strong_restrict hau hac Finset.subset_union_right

/-- An increasing exhaustion by finite globally strong substructures. -/
structure StrongExhaustion (d : Predimension V) where
  stage : ℕ → Finset V
  monotone : ∀ n m : ℕ, n ≤ m → stage n ⊆ stage m
  strong : ∀ n : ℕ, d.IsGloballyStrong (stage n)
  covers : ∀ v : V, ∃ n : ℕ, v ∈ stage n

namespace StrongExhaustion

variable {d : Predimension V}
variable (e : StrongExhaustion d)

/-- Every finite source lies in some stage of the exhaustion. -/
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
      · exact (e.monotone j (max i j) (Nat.le_max_right i j)) hj
      · exact (e.monotone i (max i j) (Nat.le_max_left i j)) (hi hws)

/-- A stage chosen to contain a given finite source. -/
noncomputable def chosenStage (s : Finset V) : ℕ :=
  Classical.choose (e.contains_finite s)

theorem chosenStage_contains (s : Finset V) :
    s ⊆ e.stage (e.chosenStage s) := by
  unfold chosenStage
  exact Classical.choose_spec (e.contains_finite s)

/-- The canonical finite strong hull of s in the infinite union. -/
noncomputable def closure (s : Finset V) : Finset V :=
  d.strongHull s (e.stage (e.chosenStage s))

theorem subset_closure (s : Finset V) : s ⊆ e.closure s := by
  exact d.subset_strongHull (e.chosenStage_contains s)

theorem closure_global (s : Finset V) :
    d.IsGloballyStrong (e.closure s) :=
  d.strongHull_global (e.strong (e.chosenStage s))

theorem closure_least_global (s b : Finset V)
    (hb : d.IsGloballyStrong b) (hsb : s ⊆ b) :
    e.closure s ⊆ b :=
  d.strongHull_least_global (e.strong (e.chosenStage s))
    (e.chosenStage_contains s) hb hsb

/-- The canonical closure agrees with the finite hull in every finite
globally strong container of the source. -/
theorem closure_eq_strongHull (s c : Finset V)
    (hc : d.IsGloballyStrong c) (hsc : s ⊆ c) :
    e.closure s = d.strongHull s c :=
  d.strongHull_eq_of_global (e.strong (e.chosenStage s)) hc
    (e.chosenStage_contains s) hsc

theorem closure_mono {s t : Finset V} (hst : s ⊆ t) :
    e.closure s ⊆ e.closure t :=
  e.closure_least_global s (e.closure t) (e.closure_global t)
    (hst.trans (e.subset_closure t))

theorem closure_idempotent (s : Finset V) :
    e.closure (e.closure s) = e.closure s := by
  apply le_antisymm
  · apply e.closure_least_global
    · exact e.closure_global s
    · intro v hv
      exact hv
  · exact e.subset_closure (e.closure s)

/-- Globally strong sets are exactly the finite closed sets. -/
theorem closure_eq_self_of_global {s : Finset V}
    (hs : d.IsGloballyStrong s) : e.closure s = s := by
  apply le_antisymm
  · apply e.closure_least_global
    · exact hs
    · intro v hv
      exact hv
  · exact e.subset_closure s

theorem global_of_closure_eq_self {s : Finset V}
    (hs : e.closure s = s) : d.IsGloballyStrong s := by
  rw [← hs]
  exact e.closure_global s

end StrongExhaustion
end Predimension
end BigHrushovski
