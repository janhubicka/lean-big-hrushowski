import BigHrushovski.CFDClosedDecomposition

/-!
# Lifting a finite d-closed extension one minimal step at a time

A finite strict d-closed extension splits into finitely many minimal
strict d-closed steps. Hence any property of partial labelled
realizations that admits extensions across *every* minimal step
admits extensions across arbitrary finite d-closed inclusions.

The proof keeps track of the prescribed source vertices:
each new map agrees with the preceding map on all previously
realized vertices, not merely up to a graph isomorphism.
It is deliberately independent of graph catalogues, growth bounds,
countable stage carriers, and fairness schedules.

To instantiate this in C_F, take Valid S f to assert that f restricted
to S is an induced embedding whose image is d-closed in a selected
ambient stage. The remaining concrete obligation is to verify the
minimal-step extension hypothesis using an actual tagged stage.
-/

namespace BigHrushovski
namespace Predimension

variable {V W : Type*} [DecidableEq V] (d : Predimension V)

/-- One-step extensions that preserve the given vertex map on
the entire previous base can be iterated over any finite chain
of minimal d-closed steps. -/
theorem MinimalDClosedChain.lift_by_minimal_steps
    (Valid : Finset V → (V → W) → Prop)
    (hLocal : ∀ {a b : Finset V},
      d.IsMinimalDClosedStep a b →
      ∀ f : V → W, Valid a f →
        ∃ g : V → W, Valid b g ∧
          ∀ v ∈ a, g v = f v)
    {a b : Finset V}
    (chain : MinimalDClosedChain d a b)
    (f : V → W) (hf : Valid a f) :
    ∃ g : V → W, Valid b g ∧ ∀ v ∈ a, g v = f v := by
  induction chain generalizing f with
  | refl a =>
      exact ⟨f, hf, by intro v _; rfl⟩
  | step hStep hTail ih =>
      obtain ⟨g, hg, hgf⟩ := hLocal hStep f hf
      obtain ⟨h, hh, hhg⟩ := ih g hg
      refine ⟨h, hh, ?_⟩
      intro v hv
      exact (hhg v (hStep.1.1 hv)).trans (hgf v hv)

/-- It suffices to respond to minimal strict d-closed
extensions in order to respond to *every* finite strict
d-closed extension over a prescribed labelled source.

The statement does not assert the local response hypothesis:
that is the construction-specific work for C_0 or C_F. -/
theorem lift_dClosed_extension_of_minimal_responses
    (Valid : Finset V → (V → W) → Prop)
    (hLocal : ∀ {a b : Finset V},
      d.IsMinimalDClosedStep a b →
      ∀ f : V → W, Valid a f →
        ∃ g : V → W, Valid b g ∧
          ∀ v ∈ a, g v = f v)
    {a b : Finset V}
    (hab : d.IsDClosed a b)
    (f : V → W) (hf : Valid a f) :
    ∃ g : V → W, Valid b g ∧ ∀ v ∈ a, g v = f v := by
  exact (d.finite_minimal_decomposition_of_dClosed_absolute hab)
    |>.lift_by_minimal_steps d Valid hLocal f hf

end Predimension
end BigHrushovski
