import BigHrushovski.FiniteDecomposition
import BigHrushovski.GenericStrongClosure

/-!
# Finite completion runs for closure-component enumerations

The minimal-increment construction in the C₀ manuscript has two
independent finite ingredients:

* Every finite globally strong prefix can be enlarged to include any
  prescribed finite set by a finite chain of minimal strong steps.
* In a minimal strong step ending at a globally strong finite set,
  every new point generates the entire step over the old prefix.

These lemmas supply the finite uninterrupted run in Lemma `exhaust`.
They do not yet construct the single omega-sequence simultaneously
scheduling all finite requests.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

/-- A chain of minimal strong steps gives an induced strong inclusion
between its endpoints. -/
theorem MinimalStrongChain.isStrong
    {a b : Finset V} (h : MinimalStrongChain d a b) :
    d.IsStrong a b := by
  induction h with
  | refl a =>
      exact d.strong_refl a
  | @step a b c hab hbc ih =>
      exact d.strong_trans hab.1 ih

namespace StrongExhaustion

/-- The new vertex in a finite minimal strong extension can be chosen
arbitrarily: each new vertex generates the whole extension over the base.

The strongness of b in the ambient structure is essential to identify
its intrinsic closure, not just a closure computed inside b. -/
theorem minimal_step_generated_by_every_new_vertex
    (e : StrongExhaustion d)
    {a b : Finset V} {x : V}
    (hab : d.IsMinimalStrongStep a b)
    (hb : d.IsGloballyStrong b)
    (hxB : x ∈ b) (hxA : x ∉ a) :
    e.closure (insert x a) = b := by
  have hGen : insert x a ⊆ b := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hya
    · exact hxB
    · exact hab.1.1 hya
  have hClB : e.closure (insert x a) ⊆ b :=
    e.closure_least_global (insert x a) b hb hGen
  have hACl : a ⊆ e.closure (insert x a) := by
    intro y hy
    exact e.subset_closure (insert x a)
      (Finset.mem_insert_of_mem hy)
  have hClStrong :
      d.IsStrong (e.closure (insert x a)) b :=
    (e.closure_global (insert x a)) b hClB
  rcases hab.2.2 (e.closure (insert x a)) hACl hClB hClStrong with
    heq | heq
  · have hxCl : x ∈ e.closure (insert x a) :=
      e.subset_closure (insert x a) (Finset.mem_insert_self x a)
    rw [heq] at hxCl
    exact (hxA hxCl).elim
  · exact heq

/-- A finite uninterrupted run can insert an arbitrary finite list of
required vertices. Every intermediate inclusion is a minimal strong
step; the final set is globally strong.

No hypothesis that the source lies in a predetermined stage is needed. -/
theorem exists_finite_minimal_run_cover
    (e : StrongExhaustion d) (a s : Finset V)
    (ha : d.IsGloballyStrong a) :
    ∃ b : Finset V,
      d.IsGloballyStrong b ∧ a ⊆ b ∧ s ⊆ b ∧
        MinimalStrongChain d a b := by
  let b := e.closure (a ∪ s)
  have hGen : a ∪ s ⊆ b := e.subset_closure (a ∪ s)
  have hAB : a ⊆ b :=
    Finset.subset_union_left.trans hGen
  have hSB : s ⊆ b :=
    Finset.subset_union_right.trans hGen
  exact ⟨b, e.closure_global (a ∪ s), hAB, hSB,
    e.finite_minimal_decomposition ha
      (e.closure_global (a ∪ s)) hAB⟩

/-- If the next requested point is absent from the strong prefix, a
finite minimal run inserts it; the terminal extension is nontrivial. -/
theorem exists_finite_minimal_run_insert
    (e : StrongExhaustion d) (a : Finset V) (x : V)
    (ha : d.IsGloballyStrong a) (hx : x ∉ a) :
    ∃ b : Finset V,
      d.IsGloballyStrong b ∧
      a ⊂ b ∧ x ∈ b ∧ MinimalStrongChain d a b := by
  obtain ⟨b, hb, hab, hxb, hchain⟩ :=
    e.exists_finite_minimal_run_cover a ({x} : Finset V) ha
  have hxB : x ∈ b :=
    hxb (Finset.mem_singleton_self x)
  have hne : a ≠ b := by
    intro heq
    have : x ∈ a := heq ▸ hxB
    exact hx this
  have hssub : a ⊂ b := Finset.ssubset_iff_subset_ne.mpr ⟨hab, hne⟩
  exact ⟨b, hb, hssub, hxB, hchain⟩

end StrongExhaustion
end Predimension

namespace FiniteCatalogue

/-- The actual countable strong Hrushovski generic has finite
uninterrupted runs of minimal closure increments inserting every
prescribed finite set from every finite globally strong prefix. -/
theorem generic_exists_finite_minimal_run_cover
    (a s : Finset ℕ)
    (ha : genericTwoSparseGraph.toPredimension.IsGloballyStrong a) :
    ∃ b : Finset ℕ,
      genericTwoSparseGraph.toPredimension.IsGloballyStrong b ∧
      a ⊆ b ∧ s ⊆ b ∧
      Predimension.MinimalStrongChain
        genericTwoSparseGraph.toPredimension a b :=
  genericStrongExhaustion.exists_finite_minimal_run_cover a s ha

/-- The actual generic can insert any vertex missing from a prescribed
finite globally strong prefix in finitely many minimal steps. -/
theorem generic_exists_finite_minimal_run_insert
    (a : Finset ℕ) (x : ℕ)
    (ha : genericTwoSparseGraph.toPredimension.IsGloballyStrong a)
    (hx : x ∉ a) :
    ∃ b : Finset ℕ,
      genericTwoSparseGraph.toPredimension.IsGloballyStrong b ∧
      a ⊂ b ∧ x ∈ b ∧
      Predimension.MinimalStrongChain
        genericTwoSparseGraph.toPredimension a b :=
  genericStrongExhaustion.exists_finite_minimal_run_insert a x ha hx

end FiniteCatalogue
end BigHrushovski
