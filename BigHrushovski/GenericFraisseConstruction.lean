import BigHrushovski.ConcreteGrowingNatResponse
import BigHrushovski.TrivialStrongRequest
import BigHrushovski.FairStageRecursion

/-!
# Constructing the countable strong generic two-sparse graph

We build a genuine sequence of finite strong graph stages on consecutive
initial segments of ℕ. Each successor responds to its fair-scheduled
strong diagram if applicable. Otherwise it responds to the universally
applicable empty diagram, providing strict growth. The one-step Nat
response theorem guarantees induced old-old adjacency and nonadjacency,
strongness of the old stage, two-sparsity and a strictly larger carrier.

The abstract recursion theorem then constructs a coherent graph on ℕ,
proves two-sparsity and establishes the labelled strong extension property
of the union.

This requires no pre-existing countable generic limit as a hypothesis.
The underlying finite one-step lemmas and the recursion are separately
audited. Identification with the strong Fraisse limit, its functional
closure expansions, and the later Ramsey/Ellentuck theorems are separate
formalization targets.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The empty graph on ℕ, with no edges. -/
def emptyNatGraph : GraphOn ℕ where
  adj _ _ := False
  symm := by
    intro _ _ h
    exact h
  irrefl := by
    intro _ h
    exact h

/-- The zero-vertex initial stage. -/
def emptyNatStage : FiniteNatStage where
  size := 0
  graph := emptyNatGraph
  sparse := by
    simpa using emptyNatGraph.twoSparse_empty
  supported := by
    intro _ _ h
    exact False.elim h

/-- Package the conclusions of a finite strong Nat extension as one
valid successor in the recursive stage construction. -/
private theorem pack_fair_successor
    (k : ℕ) (s : FiniteNatStage)
    (m : ℕ) (N : GraphOn ℕ)
    (hGrow : s.size < m)
    (hSparse : N.IsTwoSparse (Finset.range m))
    (hSupport : ∀ x y : ℕ, N.adj x y →
      x ∈ Finset.range m ∧ y ∈ Finset.range m)
    (hAgree : ∀ x ∈ Finset.range s.size,
      ∀ y ∈ Finset.range s.size,
        s.graph.adj x y ↔ N.adj x y)
    (hStrong : N.toPredimension.IsStrong
      (Finset.range s.size) (Finset.range m))
    (hRespond : ∀ req : ExtensionRequestCatalogue,
      fairRequest k = some req →
      AppliesAt s.graph (Finset.range s.size) req →
      RespondsAt N (Finset.range m) req) :
    ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t := by
  refine ⟨{ size := m, graph := N, sparse := hSparse,
    supported := hSupport }, ?_⟩
  exact ⟨hGrow, hAgree, hStrong, hRespond⟩

/-- Every finite stage has a successor satisfying strict growth,
strongness, induced coherence, and the scheduled response obligation.
The two cases are an applicable scheduled request, or a growth-only
fallback via the trivial empty strong request. -/
theorem exists_fair_strong_successor
    (k : ℕ) (s : FiniteNatStage) :
    ∃ t : FiniteNatStage, IsFairStrongSuccessor k s t := by
  classical
  cases hSchedule : fairRequest k with
  | none =>
      obtain ⟨m, N, hGrow, hSparse, hSupport, hAgree, hStrong, _⟩ :=
        exists_growing_nat_response
          s.graph s.size s.sparse trivialRequest
          (trivialRequest_applies s.graph s.size s.sparse)
      apply pack_fair_successor k s m N
        hGrow hSparse hSupport hAgree hStrong
      intro req hFair _
      have hImpossible :
          (some req : Option ExtensionRequestCatalogue) = none :=
        hFair.symm.trans hSchedule
      cases hImpossible
  | some req =>
      by_cases hApplicable :
          AppliesAt s.graph (Finset.range s.size) req
      · obtain ⟨m, N, hGrow, hSparse, hSupport, hAgree,
          hStrong, hAnswer⟩ :=
          exists_growing_nat_response
            s.graph s.size s.sparse req hApplicable
        apply pack_fair_successor k s m N
          hGrow hSparse hSupport hAgree hStrong
        intro req' hFair _
        have hEq : req' = req :=
          Option.some.inj (hFair.symm.trans hSchedule)
        subst req'
        exact hAnswer
      · obtain ⟨m, N, hGrow, hSparse, hSupport, hAgree, hStrong, _⟩ :=
          exists_growing_nat_response
            s.graph s.size s.sparse trivialRequest
            (trivialRequest_applies s.graph s.size s.sparse)
        apply pack_fair_successor k s m N
          hGrow hSparse hSupport hAgree hStrong
        intro req' hFair hApp'
        have hEq : req' = req :=
          Option.some.inj (hFair.symm.trans hSchedule)
        subst req'
        exact (hApplicable hApp').elim

/-- The countable two-sparse graph obtained by fair strong recursion. -/
noncomputable def genericTwoSparseGraph : GraphOn ℕ :=
  (coherentStagesOfSuccessors emptyNatStage
    exists_fair_strong_successor).limitGraph

/-- Every finite induced subgraph of the constructed graph has
nonnegative predimension. -/
theorem genericTwoSparseGraph_sparse (a : Finset ℕ) :
    0 ≤ genericTwoSparseGraph.predim a :=
  twoSparse_of_finiteSuccessors emptyNatStage
    exists_fair_strong_successor a

/-- Every labelled finite strong embedding into the constructed graph
extends to every prescribed finite strong extension over its source. -/
theorem genericTwoSparseGraph_strongExtension :
    HasStrongExtensionProperty genericTwoSparseGraph :=
  strongExtensionProperty_of_finiteSuccessors emptyNatStage
    exists_fair_strong_successor

end FiniteCatalogue
end BigHrushovski
