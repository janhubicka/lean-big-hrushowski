import BigHrushovski.CFDClosedDecomposition

/-!
# Compose literal finite embeddings along minimal strict d-closed steps

The earlier finite minimal-step induction uses total vertex maps
V → W, although a finite embedding is naturally defined only on
the subtype of its *current* finite source. Requiring total
maps would need an arbitrary default target vertex for all
unused source vertices and makes the extension invariant harder
to state.

This module gives the same induction directly on source subtype
maps. The family Valid(a,e) records any desired properties of
an embedding e from the *literal* finite source a: inducedness,
injectivity, strict d-closedness of its image and so on.

If every minimal d-closed step a <_d b admits a response
fixing the source embedding pointwise, then every finite
d-closed inclusion does. No ambient target vertex is chosen
for an unembedded source vertex. The proof is independent
of growth functions, graph catalogues and countability,
and can be reused in both C_0 and C_F developments.
-/

namespace BigHrushovski
namespace Predimension

variable {V W : Type*} [DecidableEq V] (d : Predimension V)

/-- The endpoints of a finite chain of minimal strict
d-closed steps are nested as literal finite vertex sets. -/
theorem MinimalDClosedChain.subset
    {a b : Finset V} (chain : MinimalDClosedChain d a b) :
    a ⊆ b := by
  induction chain with
  | refl a => exact Finset.Subset.rfl
  | step hStep hTail ih =>
      exact hStep.1.1.trans ih

/-- The dependent finite-step induction: an arbitrary property of
embeddings defined on actual finite source subtypes is preserved
through any finite chain, provided it is preserved by every
minimal strictly d-closed increment. The extension agrees on
every original labelled source vertex, not merely on an image
up to isomorphism. -/
theorem MinimalDClosedChain.lift_dependent
    (Valid : (a : Finset V) → ({v : V // v ∈ a} → W) → Prop)
    (hLocal : ∀ {a b : Finset V},
      (hab : d.IsMinimalDClosedStep a b) →
      (e : {v : V // v ∈ a} → W) →
      Valid a e →
      ∃ f : {v : V // v ∈ b} → W,
        Valid b f ∧
        (∀ v : {v : V // v ∈ a},
          f ⟨v.val, hab.1.1 v.property⟩ = e v))
    {a b : Finset V}
    (chain : MinimalDClosedChain d a b)
    (e : {v : V // v ∈ a} → W)
    (he : Valid a e) :
    ∃ f : {v : V // v ∈ b} → W,
      Valid b f ∧
      (∀ v : {v : V // v ∈ a},
        f ⟨v.val, chain.subset v.property⟩ = e v) := by
  induction chain generalizing e with
  | refl a =>
      exact ⟨e, he, by intro v; rfl⟩
  | @step a m b hab hTail ih =>
      obtain ⟨f, hf, hfa⟩ := hLocal hab e he
      obtain ⟨g, hg, hgf⟩ := ih f hf
      refine ⟨g, hg, ?_⟩
      intro v
      let vm : {v : V // v ∈ m} :=
        ⟨v.val, hab.1.1 v.property⟩
      calc
        g ⟨v.val, (MinimalDClosedChain.step hab hTail).subset
              v.property⟩ =
            g ⟨vm.val, hTail.subset vm.property⟩ := rfl
        _ = f vm := hgf vm
        _ = e v := hfa v

/-- Every finite strictly d-closed extension can be lifted by
minimal pointwise-preserving dependent responses. No arbitrary
default embedding is required outside the finite source. -/
theorem lift_dClosed_extension_dependent
    (Valid : (a : Finset V) → ({v : V // v ∈ a} → W) → Prop)
    (hLocal : ∀ {a b : Finset V},
      (hab : d.IsMinimalDClosedStep a b) →
      (e : {v : V // v ∈ a} → W) →
      Valid a e →
      ∃ f : {v : V // v ∈ b} → W,
        Valid b f ∧
        (∀ v : {v : V // v ∈ a},
          f ⟨v.val, hab.1.1 v.property⟩ = e v))
    {a b : Finset V} (hab : d.IsDClosed a b)
    (e : {v : V // v ∈ a} → W)
    (he : Valid a e) :
    ∃ f : {v : V // v ∈ b} → W,
      Valid b f ∧
      (∀ v : {v : V // v ∈ a},
        f ⟨v.val, hab.1 v.property⟩ = e v) := by
  have h := (d.finite_minimal_decomposition_of_dClosed_absolute
    hab).lift_dependent d Valid hLocal e he
  obtain ⟨f, hf, hfa⟩ := h
  refine ⟨f, hf, ?_⟩
  intro v
  exact hfa v

end Predimension
end BigHrushovski
