import BigHrushovski.C0FunctionalFairGeneric

/-!
# Track A: realizing a finite closed-base extension through a canonical stage

The actual fair countable C₀ limit already answers every finite
canonical functional extension over one of its literal finite stages.
Suppose a finite canonical amalgam K contains both a chosen stage T
and a requested finite canonical structure B, and its two full
functional embeddings identify the named closed base.

Realize K over T by the existing certified stage-extension theorem.
Composing with the embedding B → K then gives an induced embedding
of B into the limit, preserving *all complete* unary values and fixing
the prescribed base vertices pointwise.

This lemma does not assert the existence of K. It isolates the
countable response step, to be combined with the finite two-sided
amalgamation over arbitrary embedded bases.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Any two-sided finite canonical functional amalgam over an actual
stage yields a full functional embedding of its requested right
factor into the countable limit, fixing the specified old base.

No numerical base index alignment is required, and the conclusion
uses the exact same final map to witness induced adjacency, complete
unary-value transport, and pointwise base agreement. -/
theorem exists_functionalExtension_over_named_closedBase_of_stageAmalgam
    (n p : ℕ)
    (κOld : {v : ℕ // v ∈ fairGraphStages.stage n} → Fin p)
    (hOldValues : ∀ v : {v : ℕ // v ∈ fairGraphStages.stage n},
      fairUnaryStages.limitValue v.val =
        (FiniteC0.canonicalValue
          (fairGraphStages.limitGraph.pullback
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
          κOld v).image
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
    {W : Type} [Fintype W] [DecidableEq W]
    (K : GraphOn W) {q : ℕ} (κ : W → Fin q)
    (hNewStages : ∀ j : ℕ, j < q →
      FiniteC0.oldStage κ j = FiniteC0.oldStage κ (j+1) ∨
      K.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κ j)
        (FiniteC0.oldStage κ (j+1)))
    (f : {v : ℕ // v ∈ fairGraphStages.stage n} → W)
    (hf : Function.Injective f)
    (hAdjF : ∀ u v : {v : ℕ // v ∈ fairGraphStages.stage n},
      fairGraphStages.limitGraph.adj u.val v.val ↔
        K.adj (f u) (f v))
    (hValueF : ∀ u : {v : ℕ // v ∈ fairGraphStages.stage n},
      FiniteC0.canonicalValue K κ (f u) =
        (FiniteC0.canonicalValue
          (fairGraphStages.limitGraph.pullback
            (Subtype.val :
              {v : ℕ // v ∈ fairGraphStages.stage n} → ℕ))
          κOld u).image f)
    {B : Type} [Fintype B] [DecidableEq B]
    (H : GraphOn B) {m : ℕ} (κB : B → Fin m)
    (g : B → W) (hg : Function.Injective g)
    (hAdjG : ∀ a b : B, H.adj a b ↔ K.adj (g a) (g b))
    (hValueG : ∀ a : B,
      FiniteC0.canonicalValue K κ (g a) =
        (FiniteC0.canonicalValue H κB a).image g)
    {A : Type}
    (i : A → {v : ℕ // v ∈ fairGraphStages.stage n})
    (j : A → B)
    (hBase : ∀ a : A, f (i a) = g (j a)) :
    ∃ h : B → ℕ,
      Function.Injective h ∧
      (∀ a b : B,
        H.adj a b ↔ fairGraphStages.limitGraph.adj (h a) (h b)) ∧
      (∀ a : B,
        fairUnaryStages.limitValue (h a) =
          (FiniteC0.canonicalValue H κB a).image h) ∧
      (∀ a : A, h (j a) = (i a).val) := by
  classical
  obtain ⟨response, hResponseInj, hResponseGraph,
      hResponseBase, hResponseValue⟩ :=
    exists_functionalStageExtension_in_fair_limit
      n p κOld hOldValues K κ hNewStages
      f hf hAdjF hValueF
  let h : B → ℕ := response ∘ g
  refine ⟨h, hResponseInj.comp hg, ?_, ?_, ?_⟩
  · intro a b
    exact (hAdjG a b).trans (hResponseGraph (g a) (g b))
  · intro a
    calc
      fairUnaryStages.limitValue (h a) =
          (FiniteC0.canonicalValue K κ (g a)).image response :=
            hResponseValue (g a)
      _ = ((FiniteC0.canonicalValue H κB a).image g).image
          response := by rw [hValueG a]
      _ = (FiniteC0.canonicalValue H κB a).image h := by
        rw [Finset.image_image]
  · intro a
    calc
      h (j a) = response (g (j a)) := rfl
      _ = response (f (i a)) := by rw [hBase a]
      _ = (i a).val := hResponseBase (i a)

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
