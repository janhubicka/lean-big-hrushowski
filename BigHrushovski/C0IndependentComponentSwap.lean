import BigHrushovski.C0LocalFreeConverse
import BigHrushovski.C0LocalFreeMinimal
import BigHrushovski.C0NoCrossCriterion

/-!
# Interchanging consecutive independent minimal strong components

Let A be an old vertex set, and let B,C be fresh, pairwise disjoint
blocks with no graph edges between B and C. Suppose the steps

    A < A ∪ B < A ∪ B ∪ C

are both minimal strong. Then the swapped steps

    A < A ∪ C < A ∪ C ∪ B

are also minimal strong.

This is precisely the elementary adjacent interchange used to align
two witnessing component orders on a common closed functional base.
The proof needs no finite sparsity of the full ambient graph, no global
strongness, and no countable enumeration. The only graph condition
beyond the two minimal strong steps is absence of edges between B,C.

The induced full set-valued unary function is unchanged by such
an index swap because there is no direct back-edge between these two
blocks; that additional index-relabeling statement is separate.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Two consecutive nonadjacent fresh minimal strong components can
be interchanged, retaining minimality of both strict steps. -/
theorem independent_minimal_components_commute
    (A B C : Finset V)
    (hAB : Disjoint A B)
    (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hNoBC : ∀ u ∈ B, ∀ v ∈ C, ¬ G.adj u v)
    (hStepB : G.toPredimension.IsMinimalStrongStep A (A ∪ B))
    (hStepC : G.toPredimension.IsMinimalStrongStep
      (A ∪ B) ((A ∪ B) ∪ C)) :
    G.toPredimension.IsMinimalStrongStep A (A ∪ C) ∧
    G.toPredimension.IsMinimalStrongStep
      (A ∪ C) ((A ∪ C) ∪ B) := by
  have hOldC : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hxC
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact (Finset.disjoint_left.mp hAC) hxA hxC
    · exact (Finset.disjoint_left.mp hBC) hxB hxC
  have hNoC : G.NoCrossEdges (A ∪ B) (A ∪ C) := by
    apply G.noCross_of_backNeighbours (A ∪ B) A C
      Finset.subset_union_left
    intro u huC v hv hAdj
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact hvA
    · exact (hNoBC v hvB u huC (G.symm u v hAdj)).elim
  have hFirst : G.toPredimension.IsMinimalStrongStep A (A ∪ C) :=
    G.minimalStrongStep_local_of_noCross
      A (A ∪ B) C Finset.subset_union_left hOldC hNoC hStepC
  have hOldB : Disjoint (A ∪ C) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    rcases Finset.mem_union.mp hx with hxA | hxC
    · exact (Finset.disjoint_left.mp hAB) hxA hxB
    · exact (Finset.disjoint_left.mp hBC) hxB hxC
  have hNoB : G.NoCrossEdges (A ∪ C) (A ∪ B) := by
    apply G.noCross_of_backNeighbours (A ∪ C) A B
      Finset.subset_union_left
    intro u huB v hv hAdj
    rcases Finset.mem_union.mp hv with hvA | hvC
    · exact hvA
    · exact (hNoBC u huB v hvC hAdj).elim
  have hSecond :
      G.toPredimension.IsMinimalStrongStep
        (A ∪ C) ((A ∪ C) ∪ B) :=
    G.minimalStrongStep_enlarged_of_local
      A (A ∪ C) B Finset.subset_union_left hOldB hNoB hStepB
  exact ⟨hFirst, hSecond⟩

end GraphOn
end BigHrushovski
