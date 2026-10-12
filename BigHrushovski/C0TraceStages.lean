import BigHrushovski.C0BlockOffsets

/-!
# Indexing a finite strong trace by its successive stages

Every minimal strong trace has a canonical finite sequence of
successive stages: index zero gives its source, and index equal
to the number of proper steps gives its target. We use a total
accessor whose out-of-range default is the target, but certify
the minimality assertion only at indices strictly below the
genuine trace length. This avoids a gratuitous strong step at a
boundary and keeps the actual vertex sets as Finset values.

The code is independent of the choice of finite segments in
the countable C0 skeleton.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] {d : Predimension V}

namespace MinimalStrongTrace

/-- The stage reached after \`j\` minimal steps.
The terminal stage is used as the out-of-range default. -/
def at : {a b : Finset V} →
    MinimalStrongTrace d a b → ℕ → Finset V
  | _, b, .refl _, _ => b
  | a, _, .step _ _, 0 => a
  | _, _, .step _ rest, j + 1 => at rest j

theorem at_zero {a b : Finset V}
    (t : MinimalStrongTrace d a b) : t.at 0 = a := by
  cases t with
  | refl a => rfl
  | @step a b c hab rest => rfl

theorem at_last {a b : Finset V}
    (t : MinimalStrongTrace d a b) :
    t.at t.starts.length = b := by
  induction t with
  | refl a => rfl
  | @step a b c hab rest ih =>
      change rest.at rest.starts.length = c
      exact ih

/-- All genuine pairs of successive stages are minimal strong
extensions, including the last step ending at the terminal stage. -/
theorem at_minimal_step {a b : Finset V}
    (t : MinimalStrongTrace d a b) (j : ℕ)
    (hj : j < t.starts.length) :
    d.IsMinimalStrongStep (t.at j) (t.at (j + 1)) := by
  induction t generalizing j with
  | refl a =>
      simp [starts] at hj
  | @step a b c hab rest ih =>
      cases j with
      | zero =>
          change d.IsMinimalStrongStep a (rest.at 0)
          rw [at_zero]
          exact hab
      | succ j =>
          have hj' : j < rest.starts.length := by
            simpa only [starts, List.length_cons] using hj
          change d.IsMinimalStrongStep (rest.at (j + 1))
            (rest.at (j + 1 + 1))
          exact ih j hj'

end MinimalStrongTrace

end Predimension
end BigHrushovski
