import BigHrushovski.FiniteDecomposition

/-!
# From finite strong covers to countable strong exhaustions

Every finite vertex set may be contained in a finite globally strong set,
without assuming a particular increasing exhaustion. Once an explicit
surjective countable enumeration is provided, such a cover property
constructs an increasing strong exhaustion. The associated finite closure
is independent both of the selected finite container and of the exhaustion.

This theorem is a reduction. It does not establish the finite strong cover
property or the generic extension property for the concrete Hrushovski
Fraisse limit.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

/-- Every finite set lies in some finite globally strong set. -/
structure FiniteStrongCover (d : Predimension V) : Prop where
  exists_container :
    ∀ s : Finset V, ∃ c : Finset V, s ⊆ c ∧ d.IsGloballyStrong c

namespace FiniteStrongCover

variable (h : FiniteStrongCover d)

/-- A selected finite strong container; no uniqueness is assumed. -/
noncomputable def chosenContainer (s : Finset V) : Finset V :=
  Classical.choose (h.exists_container s)

theorem chosenContainer_contains (s : Finset V) :
    s ⊆ h.chosenContainer s :=
  (Classical.choose_spec (h.exists_container s)).1

theorem chosenContainer_global (s : Finset V) :
    d.IsGloballyStrong (h.chosenContainer s) :=
  (Classical.choose_spec (h.exists_container s)).2

/-- Finite strong closure obtained from arbitrary finite strong containers. -/
noncomputable def closure (s : Finset V) : Finset V :=
  d.strongHull s (h.chosenContainer s)

theorem subset_closure (s : Finset V) : s ⊆ h.closure s :=
  d.subset_strongHull (h.chosenContainer_contains s)

theorem closure_global (s : Finset V) :
    d.IsGloballyStrong (h.closure s) :=
  d.strongHull_global (h.chosenContainer_global s)

theorem closure_least_global (s b : Finset V)
    (hb : d.IsGloballyStrong b) (hsb : s ⊆ b) :
    h.closure s ⊆ b :=
  d.strongHull_least_global (h.chosenContainer_global s)
    (h.chosenContainer_contains s) hb hsb

theorem closure_mono {s t : Finset V} (hst : s ⊆ t) :
    h.closure s ⊆ h.closure t :=
  h.closure_least_global s (h.closure t) (h.closure_global t)
    (hst.trans (h.subset_closure t))

theorem closure_idempotent (s : Finset V) :
    h.closure (h.closure s) = h.closure s := by
  apply le_antisymm
  · exact h.closure_least_global _ _ (h.closure_global s) (Subset.rfl)
  · exact h.subset_closure (h.closure s)

/-- The cover-based closure equals any exhaustion-based strong closure. -/
theorem closure_eq_exhaustion (e : StrongExhaustion d)
    (s : Finset V) : h.closure s = e.closure s :=
  d.strongHull_eq_of_global
    (h.chosenContainer_global s) (e.strong (e.chosenStage s))
    (h.chosenContainer_contains s) (e.chosenStage_contains s)

end FiniteStrongCover

/-- A countable presentation with a finite strong cover property.
The enumeration is a surjection, so repetitions are allowed. -/
structure CountableStrongCover (d : Predimension V) where
  enumerate : ℕ → V
  surjective : Function.Surjective enumerate
  cover : FiniteStrongCover d

namespace CountableStrongCover

variable (h : CountableStrongCover d)

/-- Finite stages constructed by repeatedly closing the previous stage
and the next vertex in the enumeration. -/
noncomputable def stage : ℕ → Finset V
  | 0 => h.cover.chosenContainer ∅
  | n + 1 => h.cover.chosenContainer (insert (h.enumerate n) (h.stage n))

theorem stage_global (n : ℕ) :
    d.IsGloballyStrong (h.stage n) := by
  cases n with
  | zero =>
      exact h.cover.chosenContainer_global ∅
  | succ n =>
      exact h.cover.chosenContainer_global (insert (h.enumerate n) (h.stage n))

theorem stage_step (n : ℕ) :
    h.stage n ⊆ h.stage (n + 1) := by
  intro v hv
  exact (h.cover.chosenContainer_contains
    (insert (h.enumerate n) (h.stage n)))
    (Finset.mem_insert_of_mem hv)

theorem stage_monotone {n m : ℕ} (hnm : n ≤ m) :
    h.stage n ⊆ h.stage m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact Subset.rfl
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact (ih hle).trans (h.stage_step m)
      · have heq : n = m + 1 := by omega
        subst n
        exact Subset.rfl

theorem stage_covers (v : V) :
    ∃ n : ℕ, v ∈ h.stage n := by
  obtain ⟨n, hn⟩ := h.surjective v
  refine ⟨n + 1, ?_⟩
  have hin : h.enumerate n ∈ h.stage (n + 1) :=
    h.cover.chosenContainer_contains
      (insert (h.enumerate n) (h.stage n))
      (Finset.mem_insert_self (h.enumerate n) (h.stage n))
  rw [hn] at hin
  exact hin

/-- The finite-cover property produces a strong exhaustion. -/
noncomputable def toStrongExhaustion : StrongExhaustion d where
  stage := h.stage
  monotone := fun n m hnm => h.stage_monotone hnm
  strong := h.stage_global
  covers := h.stage_covers

/-- A countable finite-strong-cover structure admits an actual
increasing strong exhaustion, without assuming one as input. -/
theorem exists_strong_exhaustion :
    Nonempty (StrongExhaustion d) :=
  ⟨h.toStrongExhaustion⟩

/-- The exhaustion-based and finite-cover-based closures agree. -/
theorem exhaustion_closure_eq_cover (s : Finset V) :
    h.toStrongExhaustion.closure s = h.cover.closure s :=
  (h.cover.closure_eq_exhaustion h.toStrongExhaustion s).symm

end CountableStrongCover
end Predimension
end BigHrushovski
