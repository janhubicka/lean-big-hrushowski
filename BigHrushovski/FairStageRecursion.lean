import BigHrushovski.StageResponseLimit
import BigHrushovski.NatStageCoverage

/-!
# Recursion from finite fair successors to a countable strong generic graph

The only remaining existence obligation for the countable generic
construction can be isolated as a one-step finite existence theorem.

A finite stage consists of a graph on ℕ whose entire edge relation
is supported on a finite consecutive initial segment and whose
induced subgraph there is two-sparse. A successor must strictly
grow the segment, preserve all old-old edges and nonedges, keep
the old stage strong, and answer a scheduled request whenever it
is applicable.

Assuming a witness for each such finite successor, ordinary recursion
and classical choice construct an infinite coherent sequence. The
proved strong-limit and fair-response theorems then imply that its
union is two-sparse and has the labelled strong extension property.

This theorem is conditional ONLY on finite one-step existence.
It does not posit a countable Fraisse limit or a fair sequence.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- A two-sparse finite stage on a consecutive Nat interval. -/
structure FiniteNatStage where
  size : ℕ
  graph : GraphOn ℕ
  sparse : graph.IsTwoSparse (Finset.range size)
  supported : ∀ x y : ℕ, graph.adj x y →
    x ∈ Finset.range size ∧ y ∈ Finset.range size

/-- The exact requirements for a successor stage at schedule index k. -/
structure IsFairStrongSuccessor
    (k : ℕ) (s t : FiniteNatStage) : Prop where
  grows : s.size < t.size
  agrees : ∀ x ∈ Finset.range s.size, ∀ y ∈ Finset.range s.size,
    s.graph.adj x y ↔ t.graph.adj x y
  strong : t.graph.toPredimension.IsStrong
    (Finset.range s.size) (Finset.range t.size)
  responds : ∀ req : ExtensionRequestCatalogue,
    fairRequest k = some req →
    AppliesAt s.graph (Finset.range s.size) req →
    RespondsAt t.graph (Finset.range t.size) req

/-- Choose each finite successor separately. This choice is justified
by an explicit finite one-step existence hypothesis. -/
noncomputable def finiteStageSequence
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    ℕ → FiniteNatStage :=
  Nat.rec initial (fun k s => Classical.choose (hNext k s))

theorem finiteStageSequence_step
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t)
    (k : ℕ) :
    IsFairStrongSuccessor k
      (finiteStageSequence initial hNext k)
      (finiteStageSequence initial hNext (k + 1)) := by
  change IsFairStrongSuccessor k
    (finiteStageSequence initial hNext k)
    (Classical.choose
      (hNext k (finiteStageSequence initial hNext k)))
  exact Classical.choose_spec
    (hNext k (finiteStageSequence initial hNext k))

/-- The selected sequence strictly increases its finite stage sizes. -/
theorem finiteStageSequence_grows
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t)
    (k : ℕ) :
    (finiteStageSequence initial hNext k).size <
      (finiteStageSequence initial hNext (k + 1)).size :=
  (finiteStageSequence_step initial hNext k).grows

/-- Recursively selected stages form a coherent graph system on all
of ℕ, not merely on some infinite proper subset of the Nat carrier. -/
noncomputable def coherentStagesOfSuccessors
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    CoherentNatGraphStages where
  stage := fun k => Finset.range (finiteStageSequence initial hNext k).size
  graph := fun k => (finiteStageSequence initial hNext k).graph
  stage_step := by
    intro k
    exact FiniteSpan.initialSegment_stage_step
      (fun j => (finiteStageSequence initial hNext j).size)
      (finiteStageSequence_grows initial hNext) k
  edge_support := by
    intro k x y hadj
    exact (finiteStageSequence initial hNext k).supported x y hadj
  agrees_old := by
    intro k x y hx hy
    exact (finiteStageSequence_step initial hNext k).agrees x hx y hy
  covers := by
    exact FiniteSpan.initialSegment_stages_cover
      (fun j => (finiteStageSequence initial hNext j).size)
      (finiteStageSequence_grows initial hNext)

/-- The coherence system has strong successor inclusions. -/
theorem coherentStagesOfSuccessors_strong
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    (coherentStagesOfSuccessors initial hNext).HasStrongSteps := by
  intro k
  exact (finiteStageSequence_step initial hNext k).strong

/-- Every finite stage of the constructed system is two-sparse. -/
theorem coherentStagesOfSuccessors_sparse
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    (coherentStagesOfSuccessors initial hNext).HasTwoSparseStages := by
  intro k
  exact (finiteStageSequence initial hNext k).sparse

/-- The finite one-step existence hypothesis suffices for the strong
extension property of the constructed countable graph union. -/
theorem strongExtensionProperty_of_finiteSuccessors
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    HasStrongExtensionProperty
      (coherentStagesOfSuccessors initial hNext).limitGraph := by
  let S := coherentStagesOfSuccessors initial hNext
  apply S.strongExtensionProperty_of_stageResponses
    (coherentStagesOfSuccessors_strong initial hNext)
  intro k req hFair hApp
  exact (finiteStageSequence_step initial hNext k).responds
    req hFair hApp

/-- The same countable graph is two-sparse on every finite subset. -/
theorem twoSparse_of_finiteSuccessors
    (initial : FiniteNatStage)
    (hNext : ∀ k : ℕ, ∀ s : FiniteNatStage,
      ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t) :
    ∀ a : Finset ℕ,
      0 ≤ (coherentStagesOfSuccessors initial hNext).limitGraph.predim a :=
  CoherentNatGraphStages.limit_predim_nonneg_of_sparse_stages
    (coherentStagesOfSuccessors initial hNext)
    (coherentStagesOfSuccessors_strong initial hNext)
    (coherentStagesOfSuccessors_sparse initial hNext)

end FiniteCatalogue
end BigHrushovski
