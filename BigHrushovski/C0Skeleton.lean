import BigHrushovski.C0FiniteRuns

/-!
# A strictly increasing countable strong skeleton with minimal refinements

For every finite stage a of a graph on ℕ, there is a fresh natural
number not in a. At index n, close the old finite stage together with
both n and a fresh number. This directly yields:

* a strictly increasing sequence of finite globally strong stages;
* coverage of ℕ, since n lies in stage (n+1);
* a finite chain of minimal strong increments between successive stages.

No infinite fairness assumption or countable compactness is needed.
The remaining enumeration interface is to concatenate those finite
minimal chains into a single ω-indexed sequence (and subsequently
interleave extension requests for the unary functional structure).
-/

namespace BigHrushovski
namespace Predimension
namespace C0Skeleton

/-- No finite subset of ℕ contains every natural number. -/
theorem exists_freshNat (a : Finset ℕ) : ∃ x : ℕ, x ∉ a := by
  classical
  by_contra h
  have hall : ∀ x : ℕ, x ∈ a := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hsub : Finset.range (a.card + 1) ⊆ a := by
    intro x _
    exact hall x
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range] at hcard
  omega

/-- A specified fresh vertex, used solely to guarantee a nonempty
finite refinement at every skeleton stage. -/
noncomputable def freshNat (a : Finset ℕ) : ℕ :=
  Classical.choose (exists_freshNat a)

theorem freshNat_not_mem (a : Finset ℕ) : freshNat a ∉ a :=
  Classical.choose_spec (exists_freshNat a)

variable {d : Predimension ℕ}

/-- A concrete countable sequence of finite strong closure containers.
The first insertion at index n explicitly includes n. -/
noncomputable def stage (e : StrongExhaustion d) : ℕ → Finset ℕ
  | 0 => e.closure ∅
  | n + 1 =>
      e.closure (insert n (insert (freshNat (stage e n)) (stage e n)))

theorem stage_global (e : StrongExhaustion d) (n : ℕ) :
    d.IsGloballyStrong (stage e n) := by
  cases n with
  | zero => exact e.closure_global ∅
  | succ n => exact e.closure_global _

theorem stage_subset_succ (e : StrongExhaustion d) (n : ℕ) :
    stage e n ⊆ stage e (n + 1) := by
  intro x hx
  exact e.subset_closure _
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))

theorem fresh_mem_succ (e : StrongExhaustion d) (n : ℕ) :
    freshNat (stage e n) ∈ stage e (n + 1) :=
  e.subset_closure _
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem prescribed_mem_succ (e : StrongExhaustion d) (n : ℕ) :
    n ∈ stage e (n + 1) :=
  e.subset_closure _ (Finset.mem_insert_self _ _)

/-- The artificial fresh vertex makes the skeleton strictly increasing,
even when the prescribed index n is already in the previous closure. -/
theorem stage_strict_succ (e : StrongExhaustion d) (n : ℕ) :
    stage e n ⊂ stage e (n + 1) := by
  have hne : stage e n ≠ stage e (n + 1) := by
    intro heq
    have hNew := fresh_mem_succ e n
    rw [← heq] at hNew
    exact (freshNat_not_mem _) hNew
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨stage_subset_succ e n, hne⟩

theorem stage_strong_succ (e : StrongExhaustion d) (n : ℕ) :
    d.IsStrong (stage e n) (stage e (n + 1)) :=
  stage_global e n _ (stage_subset_succ e n)

/-- The countable, strictly increasing sequence is an actual
StrongChain. Coverage requires no diagonalization: use stage (n+1)
for vertex n. -/
noncomputable def asStrongChain (e : StrongExhaustion d) :
    StrongChain d where
  stage := stage e
  strong_step := stage_strong_succ e
  covers := by
    intro n
    exact ⟨n + 1, prescribed_mem_succ e n⟩

/-- Every individual skeleton step has a finite decomposition into
minimal strong increments. Its endpoints differ by at least one vertex. -/
theorem stage_minimal_segment (e : StrongExhaustion d) (n : ℕ) :
    MinimalStrongChain d (stage e n) (stage e (n + 1)) :=
  e.finite_minimal_decomposition
    (stage_global e n) (stage_global e (n + 1))
    (stage_subset_succ e n)

end C0Skeleton
end Predimension

namespace FiniteCatalogue

/-- A second concrete strong exhaustion of the countable generic,
chosen to have strictly growing stages and finite minimal refinements. -/
noncomputable def genericC0StrongSkeleton :
    Predimension.StrongChain genericTwoSparseGraph.toPredimension :=
  Predimension.C0Skeleton.asStrongChain genericStrongExhaustion

theorem genericC0StrongSkeleton_strict (n : ℕ) :
    genericC0StrongSkeleton.stage n ⊂
      genericC0StrongSkeleton.stage (n + 1) :=
  Predimension.C0Skeleton.stage_strict_succ genericStrongExhaustion n

theorem genericC0StrongSkeleton_minimal_segment (n : ℕ) :
    Predimension.MinimalStrongChain
      genericTwoSparseGraph.toPredimension
      (genericC0StrongSkeleton.stage n)
      (genericC0StrongSkeleton.stage (n + 1)) :=
  Predimension.C0Skeleton.stage_minimal_segment genericStrongExhaustion n

end FiniteCatalogue
end BigHrushovski
