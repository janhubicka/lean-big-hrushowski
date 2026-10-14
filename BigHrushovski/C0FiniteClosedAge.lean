import BigHrushovski.C0ClosedUnions
import BigHrushovski.C0PreparedBlocks

/-!
# Strongness of unary-closed subsets in finite block enumerations

The manuscript's functional age is defined by finite sequences of
minimal strong increments. A subset closed under the complete
component and back-neighbour dependencies either omits each block or
contains it in full, and in the latter case the selected old part
contains all old neighbours of the block.

These precise graph hypotheses are sufficient to prove that every
such selected subset is strong in the final finite graph. This is a
finite and representation-independent statement; it does not assume
the special countable generic C0 enumeration.

The functional-age application must derive the certificates from its
actual unary closure values, rather than assume them.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- A selected set s either omits a whole new block or takes it
entirely. If it takes the block, it must contain every old neighbour
of that block (the no-cross certificate). Every old-to-new step is
also strong in the graph predimension. -/
def IsClosedBlockSequence (s a : Finset V) :
    List (Finset V) → Prop
  | [] => True
  | B :: rest =>
      G.toPredimension.IsStrong a (a ∪ B) ∧
      Disjoint a B ∧
      (B ⊆ s ∨ Disjoint s B) ∧
      (B ⊆ s → G.NoCrossEdges a ((s ∩ a) ∪ B)) ∧
      G.IsClosedBlockSequence s (a ∪ B) rest

/-- The endpoint of a finite sequence of graph blocks. -/
def attachedClosedBlocks (a : Finset V) (blocks : List (Finset V)) :
    Finset V :=
  blocks.foldl (fun old B => old ∪ B) a

/-- The induction step: closure under components and old neighbours
transfers strongness of the selected vertices across a strong block
extension. -/
theorem closedSubset_strong_step
    (s a B : Finset V)
    (hOld : G.toPredimension.IsStrong (s ∩ a) a)
    (hStep : G.toPredimension.IsStrong a (a ∪ B))
    (hDisj : Disjoint a B)
    (hCase : B ⊆ s ∨ Disjoint s B)
    (hNo : B ⊆ s → G.NoCrossEdges a ((s ∩ a) ∪ B)) :
    G.toPredimension.IsStrong
      (s ∩ (a ∪ B)) (a ∪ B) := by
  rcases hCase with hAll | hNone
  · have hEq : s ∩ (a ∪ B) = (s ∩ a) ∪ B := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvS, hvAB⟩ := Finset.mem_inter.mp hv
        rcases Finset.mem_union.mp hvAB with hvA | hvB
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_inter.mpr ⟨hvS, hvA⟩))
        · exact Finset.mem_union.mpr (Or.inr hvB)
      · intro hv
        rcases Finset.mem_union.mp hv with hvOld | hvB
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hvOld).1,
             Finset.mem_union.mpr (Or.inl
               (Finset.mem_inter.mp hvOld).2)⟩
        · exact Finset.mem_inter.mpr
            ⟨hAll hvB, Finset.mem_union.mpr (Or.inr hvB)⟩
    rw [hEq]
    exact G.closedBlock_strong_of_noCross a (s ∩ a) B
      hOld hDisj (hNo hAll)
  · have hEq : s ∩ (a ∪ B) = s ∩ a := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvS, hvAB⟩ := Finset.mem_inter.mp hv
        rcases Finset.mem_union.mp hvAB with hvA | hvB
        · exact Finset.mem_inter.mpr ⟨hvS, hvA⟩
        · exact ((Finset.disjoint_left.mp hNone) hvS hvB).elim
      · intro hv
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hv).1,
           Finset.mem_union.mpr (Or.inl
             (Finset.mem_inter.mp hv).2)⟩
    rw [hEq]
    exact G.toPredimension.strong_trans hOld hStep

/-- Induction over a whole finite block enumeration: every subset
meeting the stated unary closure certificates is strong in the final
graph. The empty old base is handled by strong_refl below. -/
theorem closedSubset_strong_of_sequence
    (s : Finset V) (blocks : List (Finset V)) :
    ∀ a : Finset V,
      G.IsClosedBlockSequence s a blocks →
      G.toPredimension.IsStrong (s ∩ a) a →
      G.toPredimension.IsStrong
        (s ∩ attachedClosedBlocks a blocks)
        (attachedClosedBlocks a blocks) := by
  induction blocks with
  | nil =>
      intro a _ hBase
      exact hBase
  | cons B rest ih =>
      intro a hRun hBase
      change G.toPredimension.IsStrong a (a ∪ B) ∧
        Disjoint a B ∧
        (B ⊆ s ∨ Disjoint s B) ∧
        (B ⊆ s → G.NoCrossEdges a ((s ∩ a) ∪ B)) ∧
        G.IsClosedBlockSequence s (a ∪ B) rest at hRun
      rcases hRun with ⟨hStep, hDisj, hCase, hNo, hTail⟩
      change G.toPredimension.IsStrong
        (s ∩ attachedClosedBlocks (a ∪ B) rest)
        (attachedClosedBlocks (a ∪ B) rest)
      exact ih (a ∪ B) hTail
        (G.closedSubset_strong_step s a B hBase
          hStep hDisj hCase hNo)

/-- A finite functional presentation starting at the empty graph has
strong underlying substructures whenever the component and back-edge
closure certificates are satisfied. -/
theorem closedSubset_strong_from_empty
    (s : Finset V) (blocks : List (Finset V))
    (hRun : G.IsClosedBlockSequence s ∅ blocks) :
    G.toPredimension.IsStrong
      (s ∩ attachedClosedBlocks ∅ blocks)
      (attachedClosedBlocks ∅ blocks) := by
  exact G.closedSubset_strong_of_sequence s blocks ∅ hRun
    (by simpa using G.toPredimension.strong_refl (∅ : Finset V))

end GraphOn
end BigHrushovski
