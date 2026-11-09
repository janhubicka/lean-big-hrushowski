import BigHrushovski.C0FunctionalNatStageCanonical
import BigHrushovski.CoherentNatC0Stages

/-!
# Actual coherent graph/unary limit of the fair finite C₀ recursion

The earlier modules define a concrete recursive sequence of
finite canonical functional stages, preserve complete unary
values and graph edges/nonedges across every successor, and
transport each finite stage to its literal Nat initial segment.

We now build the actual coherent countable graph stages and
coherent finite-valued unary stages from that recursive
sequence, rather than postulating their existence. Every
finite stage has a canonical minimal-component presentation;
old stages are strong in all later stages and globally in
the limit. The entire limit unary operation has exact
finite values in each containing stage.

The remaining condition for identifying the limit graph
with M₀ is the full functional extension property. That
property must be deduced from the fair request schedule
rather than assumed from mere coherence.
-/

namespace BigHrushovski
namespace FiniteCatalogue
namespace FiniteFunctionalNatStage

/-- The actual graph stages of the recursively chosen finite
canonical functional structures, supported on consecutive
Nat intervals. -/
noncomputable def fairGraphStages : CoherentNatGraphStages where
  stage n := Finset.range (fairStages n).size
  graph n := (fairStages n).natGraph
  stage_step n := by
    exact Finset.range_mono (Nat.le_of_lt (fairStages_grows n))
  edge_support n x y h :=
    (fairStages n).natGraph_edge_support h
  agrees_old n x y hx hy :=
    natGraph_agree_of_successor (fairStages_step n)
      x y (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)
  covers := fairStages_covers

/-- The actual finite-valued unary operation of each recursive
stage. The complete old values are literally unchanged under
every later finite extension. -/
noncomputable def fairUnaryStages : CoherentNatUnaryStages where
  size n := (fairStages n).size
  value n x := (fairStages n).natValue x
  grows := fairStages_grows
  supported n x hx := (fairStages n).natValue_supported x hx
  coherent n x hx := natValue_agree_of_successor
    (fairStages_step n) x hx

/-- The graph and whole unary function are induced from the
*same* recursively constructed finite stage sequence. Each
actual finite stage has the complete canonical presentation
given by the literal Fin-to-Nat-range equivalence. -/
noncomputable def fairCoherentC0Stages : CoherentNatC0Stages where
  graph := fairGraphStages
  unary := fairUnaryStages
  sameStage := by
    intro n
    rfl
  finiteCanonical := by
    intro n
    exact (fairStages n).exists_canonical_natStage

/-- The original finite stages are strong in their successors
in the actual countable limit. This follows from complete
old unary value coherence and the canonical finite indices,
rather than being postulated for the countable construction. -/
theorem fairLimitStrongSteps :
    fairCoherentC0Stages.graph.HasStrongSteps :=
  fairCoherentC0Stages.strong_steps

/-- Every finite set of Nat vertices has a finite globally
strong cover inside the constructed countable limit graph. -/
theorem fairLimitFiniteStrongCover :
    Predimension.FiniteStrongCover
      fairCoherentC0Stages.graph.limitGraph.toPredimension :=
  fairCoherentC0Stages.limit_finiteStrongCover

/-- All finite substructures of the constructed countable
graph have exact canonical C₀ presentations, whose full
unary values agree with the actual countable limit. -/
theorem fairLimitCanonicalStages :
    FiniteC0.HasCanonicalFiniteStages
      fairCoherentC0Stages.graph.limitGraph
      fairCoherentC0Stages.unary.limitValue
      fairCoherentC0Stages.graph.stage :=
  fairCoherentC0Stages.limit_hasCanonicalFiniteStages

/-- Recognition of the actual recursively constructed C₀
graph as M₀ is now reduced to the genuine functional
extension property. The fair recurrence of finite requests
still has to be promoted to this countable statement. -/
theorem fairLimitReduct_generic_of_functionalExtension
    (hExt : FiniteC0.HasCanonicalStageExtensionProperty
      fairCoherentC0Stages.graph.limitGraph
      fairCoherentC0Stages.unary.limitValue
      fairCoherentC0Stages.graph.stage) :
    ∃ e : ℕ ≃ ℕ, ∀ x y : ℕ,
      FiniteCatalogue.genericTwoSparseGraph.adj x y ↔
        fairCoherentC0Stages.graph.limitGraph.adj (e x) (e y) :=
  fairCoherentC0Stages.limit_reduct_iso_generic_of_functionalExtension hExt

end FiniteFunctionalNatStage
end FiniteCatalogue
end BigHrushovski
