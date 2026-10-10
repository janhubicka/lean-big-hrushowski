import BigHrushovski.InitialSegmentLabels

/-!
# Exhaustion of ℕ by strictly growing initial-segment stages

A finite strongly growing construction is not automatically a chain
covering ℕ unless its labels have no gaps. In the initial-segment
normal form, strict size growth forces every natural number to occur
at a finite stage.

These elementary arithmetic lemmas isolate the coverage proof from
the graph predimension and genericity arguments.
-/

namespace BigHrushovski
namespace FiniteSpan

/-- A sequence of natural sizes increasing at every step satisfies
n ≤ size n even without assuming a nonempty initial stage. -/
theorem stage_index_le_size
    (size : ℕ → ℕ)
    (hGrow : ∀ n : ℕ, size n < size (n + 1)) :
    ∀ n : ℕ, n ≤ size n := by
  intro n
  induction n with
  | zero =>
      exact Nat.zero_le _
  | succ n ih =>
      have h := hGrow n
      omega

/-- Each finite initial segment is included in its successor. -/
theorem initialSegment_stage_step
    (size : ℕ → ℕ)
    (hGrow : ∀ n : ℕ, size n < size (n + 1))
    (n : ℕ) :
    Finset.range (size n) ⊆ Finset.range (size (n + 1)) := by
  intro x hx
  exact Finset.mem_range.mpr
    ((Finset.mem_range.mp hx).trans (hGrow n))

/-- If stage domains are the consecutive initial segments
range(size n) and sizes strictly grow, they cover all of ℕ. -/
theorem initialSegment_stages_cover
    (size : ℕ → ℕ)
    (hGrow : ∀ n : ℕ, size n < size (n + 1)) :
    ∀ x : ℕ, ∃ n : ℕ, x ∈ Finset.range (size n) := by
  intro x
  refine ⟨x + 1, Finset.mem_range.mpr ?_⟩
  have h := stage_index_le_size size hGrow (x + 1)
  omega

end FiniteSpan
end BigHrushovski
