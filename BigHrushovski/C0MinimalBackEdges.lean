import BigHrushovski.C0Neighbours
import BigHrushovski.MinimalExtensions

/-!
# The two-back-edge bound for minimal strong increments

This isolates the exact finite statement of Proposition twoedges in
the manuscript's C₀ enumeration. The first inequality needs only a
globally strong old prefix. To obtain the singleton component when
equality holds, one must *also* use the minimal-choice condition:
every new vertex generates the same closure over the old prefix.

We work with old neighbours in an undirected simple graph, so no
orientation or ordering of the back edges is introduced.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Every fresh vertex has at most two old neighbours when the old
finite prefix is globally strong, without specifying an extension. -/
theorem oldNeighbours_card_le_two_of_global
    {a : Finset V} {x : V}
    (ha : G.toPredimension.IsGloballyStrong a)
    (hx : x ∉ a) :
    (G.oldNeighbours a x).card ≤ 2 := by
  have hSub : a ⊆ insert x a := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  have hStrong : G.toPredimension.IsStrong a (insert x a) :=
    ha (insert x a) hSub
  exact G.oldNeighbours_card_le_two hStrong
    (Finset.mem_insert_self x a) hx

/-- In a minimal strong increment, two old neighbours imply that the
whole new component consists of this vertex. This strengthens the
generic closure identity, which by itself does not mention the
minimal generator chosen from the finite strong requirement. -/
theorem minimal_increment_singleton_of_two_oldNeighbours
    (ex : Predimension.StrongExhaustion G.toPredimension)
    {a D : Finset V} {v x : V}
    (ha : G.toPredimension.IsGloballyStrong a)
    (hD : G.toPredimension.IsGloballyStrong D)
    (haD : a ⊆ D)
    (hchoice : ex.IsMinimalChoice a D v)
    (hx : x ∈ ex.closure (insert v a))
    (hxA : x ∉ a)
    (hTwo : (G.oldNeighbours a x).card = 2) :
    ex.closure (insert v a) = insert x a := by
  have hEqual :=
    ex.equal_closure_of_minimal_choice hD haD hchoice hx hxA
  have hOne :=
    G.closure_insert_of_two_oldNeighbours ex ha hxA hTwo
  exact hEqual.symm.trans hOne

end GraphOn
end BigHrushovski
