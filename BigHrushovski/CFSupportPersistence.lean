import BigHrushovski.CFLocalSupport

/-!
# Persistence of exact finite d-closed supports under free attachments

A finite d-closed support P≤d A can be used in a larger old
graph A without changing the least strict d-closed hull of
any subset of P.  If a new block B has no neighbour in
A\P, its old-neighbour set is also unchanged.

Consequently a minimal local d-closed block with exact support
P remains a minimal d-closed extension of A, and the canonical
support computed in A is still exactly P.  The other free
factor P∪B remains d-closed as well.

These are finite graph statements. In particular they do not
assert closure of the growth-function class C_F under free
amalgamation or construct countable levels.
-/

namespace BigHrushovski

namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- A least finite strict d-closed hull is unchanged when its
ambient set is enlarged from P to A with P≤d A.  The generating
set S must already be contained in P. -/
theorem dClosedHull_restrict_of_dClosed
    (S P A : Finset V)
    (hSP : S ⊆ P) (hPA : d.IsDClosed P A) :
    d.dClosedHull S A = d.dClosedHull S P := by
  have hBigClosed : d.IsDClosed (d.dClosedHull S A) A :=
    d.dClosedHull_dclosed S A
  have hBigSubP : d.dClosedHull S A ⊆ P :=
    d.dClosedHull_least hSP hPA
  have hBigClosedP : d.IsDClosed (d.dClosedHull S A) P :=
    d.dclosed_restrict hBigClosed hBigSubP hPA.1
  have hSBig : S ⊆ d.dClosedHull S A :=
    d.subset_dClosedHull (hSP.trans hPA.1)
  have hSmallSubBig : d.dClosedHull S P ⊆ d.dClosedHull S A :=
    d.dClosedHull_least hSBig hBigClosedP
  have hSmallClosedA : d.IsDClosed (d.dClosedHull S P) A :=
    d.dclosed_trans (d.dClosedHull_dclosed S P) hPA
  have hSSmall : S ⊆ d.dClosedHull S P :=
    d.subset_dClosedHull hSP
  have hBigSubSmall : d.dClosedHull S A ⊆ d.dClosedHull S P :=
    d.dClosedHull_least hSSmall hSmallClosedA
  exact le_antisymm hBigSubSmall hSmallSubBig

end Predimension

namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- If all neighbours of B in A lie in P⊆A, the actual set
of old neighbours of B is the same when computed in A or P.
There is no closure or predimension hypothesis. -/
theorem oldNeighbourSet_eq_of_backNeighbours
    (P A B : Finset V)
    (hPA : P ⊆ A)
    (hBack : ∀ u ∈ B, ∀ v ∈ A, G.adj u v → v ∈ P) :
    G.oldNeighbourSet A B = G.oldNeighbourSet P B := by
  classical
  ext v
  simp only [oldNeighbourSet, Finset.mem_filter]
  constructor
  · rintro ⟨hvA, u, huB, hAdj⟩
    exact ⟨hBack u huB v hvA hAdj, u, huB, hAdj⟩
  · rintro ⟨hvP, h⟩
    exact ⟨hPA hvP, h⟩

/-- Reusable one-block level-attachment lemma.

If a local minimal d-closed increment over P has exact
old-neighbour support P, then it still has that precise
support after free attachment to a larger d-closed old
graph A. The enlarged step is minimal, and the local
factor remains strictly d-closed in the whole join. -/
theorem minimalLocalDClosed_support_persists
    (P A B : Finset V)
    (hPclosed : G.toPredimension.IsDClosed P A)
    (hDisj : Disjoint A B)
    (hBack : ∀ u ∈ B, ∀ v ∈ A, G.adj u v → v ∈ P)
    (hMin : G.toPredimension.IsMinimalDClosedStep P (P ∪ B))
    (hSupport : G.toPredimension.dClosedHull
      (G.oldNeighbourSet P B) P = P) :
    G.NoCrossEdges A (P ∪ B) ∧
    G.toPredimension.IsMinimalDClosedStep A (A ∪ B) ∧
    G.toPredimension.IsDClosed (P ∪ B) (A ∪ B) ∧
    G.toPredimension.dClosedHull
      (G.oldNeighbourSet A B) A = P := by
  let d := G.toPredimension
  have hPA : P ⊆ A := hPclosed.1
  have hNo : G.NoCrossEdges A (P ∪ B) :=
    G.noCross_of_backNeighbours A P B hPA hBack
  have hGlobal : d.IsMinimalDClosedStep A (A ∪ B) :=
    (G.minimalDClosedStep_free_iff P A B hPA hDisj hNo).mp hMin
  have hFactor : d.IsDClosed (P ∪ B) (A ∪ B) :=
    G.dClosed_local_right_factor P A B hPA hDisj hNo hPclosed
  have hNeighbours : G.oldNeighbourSet A B =
      G.oldNeighbourSet P B :=
    G.oldNeighbourSet_eq_of_backNeighbours P A B hPA hBack
  have hNP : G.oldNeighbourSet P B ⊆ P :=
    G.oldNeighbourSet_subset P B
  have hHull : d.dClosedHull (G.oldNeighbourSet P B) A =
      d.dClosedHull (G.oldNeighbourSet P B) P :=
    d.dClosedHull_restrict_of_dClosed
      (G.oldNeighbourSet P B) P A hNP hPclosed
  refine ⟨hNo, hGlobal, hFactor, ?_⟩
  rw [hNeighbours, hHull]
  exact hSupport

end GraphOn
end BigHrushovski
