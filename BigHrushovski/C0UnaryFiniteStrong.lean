import BigHrushovski.C0FiniteClosedAge
import BigHrushovski.C0NoCrossCriterion

/-!
# Finite unary closure supplies complete-block strongness certificates

The abstract finite closed-block theorem previously required, as
separate hypotheses for every step of an enumeration, that a selected
closed set either takes the entire block or misses it and that all old
neighbours of each selected block lie in the selected old part.

For the C0 unary function these properties follow from two
pointwise facts:
* every vertex's function value contains its complete component;
* the function value contains each of that vertex's old neighbours.

The lemmas below derive the exact no-cross certificates from these
facts and from closure under the named unary function. This works for
arbitrary finite graph block sequences, independently of the
particular countable M0 enumeration.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- A finite set is closed under the complete set-valued unary
function C, not merely under individual graph neighbours. -/
def IsClosedUnderValues (G : GraphOn V) (C : V → Finset V) (s : Finset V) : Prop :=
  ∀ u ∈ s, C u ⊆ s

/-- A finite strong block enumeration carries enough local unary
closure information: C(u) contains the whole block of u and
every old neighbour of u. No global strongness is assumed. -/
def HasUnaryBlockPresentation (G : GraphOn V) (C : V → Finset V)
    (a : Finset V) : List (Finset V) → Prop
  | [] => True
  | B :: rest =>
      G.toPredimension.IsStrong a (a ∪ B) ∧
      Disjoint a B ∧
      (∀ u ∈ B, B ⊆ C u) ∧
      (∀ u ∈ B, ∀ v ∈ a, G.adj u v → v ∈ C u) ∧
      G.HasUnaryBlockPresentation C (a ∪ B) rest

/-- Closure under the named function forces either the whole new
component or none of it to occur in a finite selected set. -/
theorem closedUnderValues_block_dichotomy
    (C : V → Finset V) (s B : Finset V)
    (hClosed : G.IsClosedUnderValues C s)
    (hWhole : ∀ u ∈ B, B ⊆ C u) :
    B ⊆ s ∨ Disjoint s B := by
  by_cases hMeet : (s ∩ B).Nonempty
  · obtain ⟨u, hu⟩ := hMeet
    have huS : u ∈ s := (Finset.mem_inter.mp hu).1
    have huB : u ∈ B := (Finset.mem_inter.mp hu).2
    exact Or.inl ((hWhole u huB).trans (hClosed u huS))
  · right
    apply Finset.disjoint_left.mpr
    intro u huS huB
    exact hMeet ⟨u, Finset.mem_inter.mpr ⟨huS, huB⟩⟩

/-- If an entire block is selected, closure under C contains all its
old neighbours. Thus there are no graph edges across the omitted-old
versus newly-selected tails. -/
theorem closedUnderValues_block_noCross
    (C : V → Finset V) (s a B : Finset V)
    (hClosed : G.IsClosedUnderValues C s)
    (hBack : ∀ u ∈ B, ∀ v ∈ a, G.adj u v → v ∈ C u)
    (hB : B ⊆ s) :
    G.NoCrossEdges a ((s ∩ a) ∪ B) := by
  apply G.noCross_of_backNeighbours a (s ∩ a) B
    Finset.inter_subset_right
  intro u huB v hvOld hAdj
  have huS : u ∈ s := hB huB
  have hvC : v ∈ C u := hBack u huB v hvOld hAdj
  exact Finset.mem_inter.mpr ⟨hClosed u huS hvC, hvOld⟩

/-- Every unary-closed selected set automatically satisfies the
complete-component and no-cross conditions required by the
finite closed-block strongness induction. -/
theorem closedUnderValues_blockSequence
    (C : V → Finset V) (s : Finset V)
    (hClosed : G.IsClosedUnderValues C s)
    (blocks : List (Finset V)) :
    ∀ a : Finset V,
      G.HasUnaryBlockPresentation C a blocks →
      G.IsClosedBlockSequence s a blocks := by
  induction blocks with
  | nil =>
      intro a _
      trivial
  | cons B rest ih =>
      intro a hRun
      change G.toPredimension.IsStrong a (a ∪ B) ∧
        Disjoint a B ∧
        (∀ u ∈ B, B ⊆ C u) ∧
        (∀ u ∈ B, ∀ v ∈ a, G.adj u v → v ∈ C u) ∧
        G.HasUnaryBlockPresentation C (a ∪ B) rest at hRun
      rcases hRun with ⟨hStep, hDisj, hWhole, hBack, hTail⟩
      change G.toPredimension.IsStrong a (a ∪ B) ∧
        Disjoint a B ∧
        (B ⊆ s ∨ Disjoint s B) ∧
        (B ⊆ s → G.NoCrossEdges a ((s ∩ a) ∪ B)) ∧
        G.IsClosedBlockSequence s (a ∪ B) rest
      exact ⟨hStep, hDisj,
        G.closedUnderValues_block_dichotomy C s B hClosed hWhole,
        G.closedUnderValues_block_noCross C s a B hClosed hBack,
        ih (a ∪ B) hTail⟩

/-- Every finite set closed under a unary function recording whole
components and their old neighbours is strong in the presented
finite graph. No ambient genericity or strong exhaustion occurs
in this theorem. -/
theorem closedUnderValues_strong_from_empty
    (C : V → Finset V) (s : Finset V)
    (blocks : List (Finset V))
    (hClosed : G.IsClosedUnderValues C s)
    (hRun : G.HasUnaryBlockPresentation C ∅ blocks) :
    G.toPredimension.IsStrong
      (s ∩ attachedClosedBlocks ∅ blocks)
      (attachedClosedBlocks ∅ blocks) := by
  exact G.closedSubset_strong_from_empty s blocks
    (G.closedUnderValues_blockSequence C s hClosed blocks ∅ hRun)

end GraphOn
end BigHrushovski
