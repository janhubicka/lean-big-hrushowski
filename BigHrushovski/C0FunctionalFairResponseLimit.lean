import BigHrushovski.C0FunctionalFairLimit
import BigHrushovski.C0FunctionalFairPersistence

/-!
# Transport an actual finite C₀ functional response to the countable limit

The fair recurrence constructs a finite strong induced complete-functional
target copy whenever a scheduled request is applicable at a finite stage.
The coherent graph/unary limit has exactly the finite graph and the
entire finite unary values on that stage. Thus the target copy remains
an induced functional embedding in the countable limit, and the original
source's prescribed numerical labels remain unchanged.

This is the finite-to-countable response interface, not an assertion
that every arbitrary countable-limit functional extension has already
been encoded in the fair request catalogue.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- Every finite strong functional response is also a complete
functional response in the actual coherent countable limit.
Its target map is the *literal* old-stage numeric value map,
so it preserves each prescribed source label pointwise. -/
theorem response_in_fair_countable_limit
    (step : ℕ) (req : FunctionalC0RequestCatalogue)
    (hResp : (fairStages step).Responds req) :
    ∃ g : Fin req.2.2.1 → ℕ,
      Function.Injective g ∧
      (∀ x y : Fin req.2.2.1,
        req.diagram.target.graph.adj x y ↔
          fairGraphStages.limitGraph.adj (g x) (g y)) ∧
      (∀ x : Fin req.2.2.1,
        fairUnaryStages.limitValue (g x) =
          (req.diagram.target.unaryValue x).image g) ∧
      (∀ x : Fin req.1,
        g (req.diagram.embedding x) = req.labels x) := by
  classical
  obtain ⟨target, hInjective, hAdj, hValues, hLabels, _⟩ := hResp
  let g : Fin req.2.2.1 → ℕ := fun x => (target x).val
  refine ⟨g, (fin_val_injective _).comp hInjective, ?_, ?_, ?_⟩
  · intro x y
    calc
      req.diagram.target.graph.adj x y ↔
          (fairStages step).model.graph.adj
            (target x) (target y) := hAdj x y
      _ ↔ (fairStages step).natGraph.adj
          (target x).val (target y).val :=
            (fairStages step).natGraph_induced (target x) (target y)
      _ ↔ fairGraphStages.limitGraph.adj (g x) (g y) := by
            have hx : (target x).val ∈
                fairGraphStages.stage step :=
              Finset.mem_range.mpr (target x).isLt
            have hy : (target y).val ∈
                fairGraphStages.stage step :=
              Finset.mem_range.mpr (target y).isLt
            exact (fairGraphStages.limitGraph_induced step hx hy).symm
  · intro x
    have hx : (target x).val < (fairStages step).size :=
      (target x).isLt
    calc
      fairUnaryStages.limitValue (g x) =
          (fairStages step).natValue (target x).val :=
            fairUnaryStages.limitValue_eq_stage step (target x).val hx
      _ = ((fairStages step).model.unaryValue (target x)).image
          (fun z : Fin (fairStages step).size => z.val) := by
            exact (fairStages step).natValue_inside (target x).val hx
      _ = ((req.diagram.target.unaryValue x).image target).image
          (fun z : Fin (fairStages step).size => z.val) := by
            rw [hValues x]
      _ = (req.diagram.target.unaryValue x).image g := by
            rw [Finset.image_image]
  · intro x
    exact hLabels x

/-- A finite labelled functional request applicable at some chosen
stage has a full induced functional target copy in the countable
limit after a later scheduled response. -/
theorem eventually_answered_in_fair_limit
    (req : FunctionalC0RequestCatalogue)
    (n : ℕ) (hApp : (fairStages n).Applies req) :
    ∃ g : Fin req.2.2.1 → ℕ,
      Function.Injective g ∧
      (∀ x y : Fin req.2.2.1,
        req.diagram.target.graph.adj x y ↔
          fairGraphStages.limitGraph.adj (g x) (g y)) ∧
      (∀ x : Fin req.2.2.1,
        fairUnaryStages.limitValue (g x) =
          (req.diagram.target.unaryValue x).image g) ∧
      (∀ x : Fin req.1,
        g (req.diagram.embedding x) = req.labels x) := by
  obtain ⟨step, _, hResponse⟩ :=
    fairStages_eventually_answers req n hApp
  exact response_in_fair_countable_limit (step+1) req hResponse

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
