import BigHrushovski.C0FunctionalFairRecursion

/-!
# Persistence and eventual response of labelled functional C₀ requests

An exact finite functional embedding of a request's source persists
through every later chosen finite stage, because successor maps
fix all old numerical labels, reflect all graph edges and nonedges,
and preserve complete one-generated unary values by equality.

The independently verified fair request catalogue revisits each
request after any chosen threshold. Thus any request applicable in
one finite stage is answered by an induced strong complete-functional
target copy at some later stage.

This is an eventual finite-response theorem. It does not yet assert
the corresponding extension property of the countable union,
which also requires exact inducedness and full unary-value
agreement between finite stages and the limit.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Functional applicability is preserved by any certified finite
successor. The image source map is the old embedding composed with
the existing labelled source map, so every original numeric label
is retained pointwise. -/
theorem applies_of_successor
    {step : ℕ} {s t : FiniteFunctionalNatStage}
    (h : IsFairFunctionalSuccessor step s t)
    (req : FunctionalC0RequestCatalogue)
    (hApp : s.Applies req) :
    t.Applies req := by
  classical
  obtain ⟨e, he, hLabels, hGraph, hValues⟩ := hApp
  refine ⟨h.old ∘ e, h.old_injective.comp he, ?_, ?_, ?_⟩
  · intro x
    change (h.old (e x)).val = req.labels x
    exact (h.old_labels (e x)).trans (hLabels x)
  · intro x y
    exact (hGraph x y).trans (h.old_graph (e x) (e y))
  · intro x
    change t.model.unaryValue (h.old (e x)) =
      (req.diagram.source.unaryValue x).image (h.old ∘ e)
    calc
      t.model.unaryValue (h.old (e x)) =
        (s.model.unaryValue (e x)).image h.old :=
          h.old_values (e x)
      _ = ((req.diagram.source.unaryValue x).image e).image
          h.old := by rw [hValues x]
      _ = (req.diagram.source.unaryValue x).image
          (h.old ∘ e) := by
            rw [Finset.image_image]

/-- Exact functional applicability persists from one chosen
finite stage to *every later* chosen finite stage. -/
theorem applies_of_le
    (req : FunctionalC0RequestCatalogue)
    {n m : ℕ} (hnm : n ≤ m)
    (hApp : (fairStages n).Applies req) :
    (fairStages m).Applies req := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact hApp
  | succ m ih =>
      by_cases hle : n ≤ m
      · exact applies_of_successor (fairStages_step m)
          req (ih hle)
      · have hn : n = m + 1 := by omega
        subst n
        exact hApp

/-- Every functional request applicable in one finite stage
is answered by a finite strong induced functional copy at some
later fair-scheduled stage, with all old labels unchanged. -/
theorem fairStages_eventually_answers
    (req : FunctionalC0RequestCatalogue)
    (n : ℕ)
    (hApp : (fairStages n).Applies req) :
    ∃ step : ℕ,
      n ≤ step ∧ (fairStages (step + 1)).Responds req := by
  obtain ⟨step, hLater, hScheduled⟩ :=
    fairFunctionalC0Request_after req n
  refine ⟨step, hLater, ?_⟩
  exact fairStages_responds step req hScheduled
    (applies_of_le req hLater hApp)

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
