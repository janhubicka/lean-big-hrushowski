import BigHrushovski.GenericFraisseConstruction
import BigHrushovski.GlobalClosure

/-!
# Finite globally strong closures in the constructed generic graph

The countable graph constructed by fair finite strong recursion has an
increasing exhaustive sequence of finite induced stages, each globally
self-sufficient. The abstract hull theorems in `GlobalClosure.lean`
therefore specialize to the actual generic structure.

In particular every finite set has a least finite globally strong
closure. This is the finite-container input needed in the strong
back-and-forth argument: an arbitrary finite domain plus one requested
vertex may not itself be globally strong.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The strongly exhaustive sequence of finite stages used to build
the generic graph, now viewed as a finite strong exhaustion of ℕ. -/
noncomputable def genericStrongExhaustion :
    Predimension.StrongExhaustion
      genericTwoSparseGraph.toPredimension :=
  ((coherentStagesOfSuccessors emptyNatStage
      exists_fair_strong_successor).asStrongChain
    (coherentStagesOfSuccessors_strong emptyNatStage
      exists_fair_strong_successor)).toStrongExhaustion

/-- Each finite set of vertices lies inside a finite globally strong
subgraph of the actual generic. -/
theorem genericTwoSparseGraph_finiteStrongCover :
    Predimension.FiniteStrongCover
      genericTwoSparseGraph.toPredimension :=
  genericStrongExhaustion.toFiniteStrongCover

/-- The least finite globally strong closure of a finite vertex set. -/
noncomputable def genericStrongClosure (s : Finset ℕ) : Finset ℕ :=
  genericStrongExhaustion.closure s

theorem subset_genericStrongClosure (s : Finset ℕ) :
    s ⊆ genericStrongClosure s :=
  genericStrongExhaustion.subset_closure s

theorem genericStrongClosure_global (s : Finset ℕ) :
    genericTwoSparseGraph.toPredimension.IsGloballyStrong
      (genericStrongClosure s) :=
  genericStrongExhaustion.closure_global s

/-- Minimality is with respect to all finite globally strong containers,
not only the selected finite stage from the construction. -/
theorem genericStrongClosure_least (s c : Finset ℕ)
    (hc : genericTwoSparseGraph.toPredimension.IsGloballyStrong c)
    (hsc : s ⊆ c) :
    genericStrongClosure s ⊆ c :=
  genericStrongExhaustion.closure_least_global s c hc hsc

theorem genericStrongClosure_mono {s t : Finset ℕ}
    (hst : s ⊆ t) :
    genericStrongClosure s ⊆ genericStrongClosure t :=
  genericStrongExhaustion.closure_mono hst

theorem genericStrongClosure_idempotent (s : Finset ℕ) :
    genericStrongClosure (genericStrongClosure s) =
      genericStrongClosure s :=
  genericStrongExhaustion.closure_idempotent s

theorem genericStrongClosure_eq_self_iff (s : Finset ℕ) :
    genericStrongClosure s = s ↔
      genericTwoSparseGraph.toPredimension.IsGloballyStrong s := by
  constructor
  · exact genericStrongExhaustion.global_of_closure_eq_self
  · exact genericStrongExhaustion.closure_eq_self_of_global

end FiniteCatalogue
end BigHrushovski
