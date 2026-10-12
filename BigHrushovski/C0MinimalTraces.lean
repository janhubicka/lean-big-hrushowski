import BigHrushovski.C0Skeleton

/-!
# Finite list witnesses for minimal strong chains

The relation `MinimalStrongChain` is a proposition, so its proof
must not be recursively eliminated into a list. This module instead
proves existence of an explicitly data-valued trace in Prop,
then chooses one by Classical.choice. All resulting finite traces
carry the same minimal-step certificates.

Each trace has a list of *starting* stages, excluding its terminal
stage, so lists of successive traces can be concatenated without
duplicating a boundary stage. There is at least one list element
when the source and target are distinct.

The actual C₀ skeleton supplies a nonempty finite trace at each
index. Flattening all those traces to a single omega sequence is
the next separate formalization obligation.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

/-- A data-valued finite chain, retaining a proof of minimality for
every successive pair. This is not a Prop-valued proof object. -/
inductive MinimalStrongTrace (d : Predimension V) :
    Finset V → Finset V → Type _ where
  | refl (a : Finset V) : MinimalStrongTrace d a a
  | step {a b c : Finset V}
      (hab : d.IsMinimalStrongStep a b)
      (rest : MinimalStrongTrace d b c) :
      MinimalStrongTrace d a c

/-- A list of the *starting* stages of consecutive minimal strong
steps from a to b. The empty list is allowed only for a=b. -/
inductive MinimalStepList (d : Predimension V) :
    Finset V → List (Finset V) → Finset V → Prop where
  | refl (a : Finset V) : MinimalStepList d a [] a
  | step {a b c : Finset V} {xs : List (Finset V)}
      (hab : d.IsMinimalStrongStep a b)
      (rest : MinimalStepList d b xs c) :
      MinimalStepList d a (a :: xs) c

namespace MinimalStrongChain

/-- Elimination stays in Prop: each propositional minimal chain
has a finite data-valued witness, but we do not directly compute
Type-valued data by pattern matching a proof in Prop. -/
theorem existsTrace {a b : Finset V}
    (h : MinimalStrongChain d a b) :
    Nonempty (MinimalStrongTrace d a b) := by
  induction h with
  | refl a =>
      exact ⟨MinimalStrongTrace.refl a⟩
  | @step a b c hab hbc ih =>
      obtain ⟨t⟩ := ih
      exact ⟨MinimalStrongTrace.step hab t⟩

/-- Noncomputable choice of a concrete finite trace. -/
noncomputable def chooseTrace {a b : Finset V}
    (h : MinimalStrongChain d a b) :
    MinimalStrongTrace d a b :=
  Classical.choice (existsTrace h)

end MinimalStrongChain

namespace MinimalStrongTrace

/-- The list of sources of the finite minimal steps; the last
terminal stage is excluded to avoid duplication under concatenation. -/
def starts : {a b : Finset V} →
    MinimalStrongTrace d a b → List (Finset V)
  | _, _, .refl _ => []
  | a, _, .step _ rest => a :: starts rest

theorem starts_valid {a b : Finset V}
    (t : MinimalStrongTrace d a b) :
    MinimalStepList d a t.starts b := by
  induction t with
  | refl a =>
      exact MinimalStepList.refl a
  | @step a b c hab rest ih =>
      exact MinimalStepList.step hab ih

theorem starts_length_pos {a b : Finset V}
    (t : MinimalStrongTrace d a b)
    (hne : a ≠ b) :
    0 < t.starts.length := by
  cases t with
  | refl a =>
      exact (hne rfl).elim
  | @step a b c hab rest =>
      simp [starts]

end MinimalStrongTrace

namespace MinimalStepList

/-- Concatenating lists witnessing consecutive finite runs
preserves every minimal-step certificate across the joint boundary. -/
theorem append {a b c : Finset V}
    {xs ys : List (Finset V)}
    (h : MinimalStepList d a xs b)
    (k : MinimalStepList d b ys c) :
    MinimalStepList d a (xs ++ ys) c := by
  induction h generalizing ys c with
  | refl a =>
      simpa using k
  | @step a b z xs hab rest ih =>
      exact MinimalStepList.step hab (ih k)

end MinimalStepList
end Predimension

namespace FiniteCatalogue

/-- A chosen finite trace that decomposes an individual step of
the *actual* strongly exhaustive C₀ skeleton into minimal steps. -/
noncomputable def genericC0SegmentTrace (n : ℕ) :
    Predimension.MinimalStrongTrace
      genericTwoSparseGraph.toPredimension
      (genericC0StrongSkeleton.stage n)
      (genericC0StrongSkeleton.stage (n + 1)) :=
  Predimension.MinimalStrongChain.chooseTrace
    (genericC0StrongSkeleton_minimal_segment n)

/-- Every skeleton interval contributes at least one minimal
strong step to the planned omega-concatenation. -/
theorem genericC0SegmentTrace_nonempty (n : ℕ) :
    0 < (genericC0SegmentTrace n).starts.length := by
  have hne :
      genericC0StrongSkeleton.stage n ≠
        genericC0StrongSkeleton.stage (n + 1) :=
    (Finset.ssubset_iff_subset_ne.mp
      (genericC0StrongSkeleton_strict n)).2
  exact Predimension.MinimalStrongTrace.starts_length_pos
    (genericC0SegmentTrace n) hne

end FiniteCatalogue
end BigHrushovski
