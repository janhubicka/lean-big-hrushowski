import BigHrushovski.CFClosedFactor
import BigHrushovski.CFDClosedGenerators
import BigHrushovski.C0NoCrossCriterion

/-!
# Canonical finite local support of a minimal d-closed increment

For a minimal strict d-closed graph extension A <_d A∪B,
let N be the set of old vertices adjacent to B and put
P = cl^d_A(N). This P is exactly the least d-closed old support.

The extension is the graph free amalgam of A and P∪B over P;
P <_d P∪B is again minimal, both factors are d-closed
in the whole graph, and cl^d_P(N)=P.

The proof does not assume membership in any particular C_F class.
The class-level amalgamation theorem, countable generic and
functional block-root reconstruction remain separate.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Old vertices adjacent to at least one new vertex. -/
noncomputable def oldNeighbourSet (A B : Finset V) : Finset V := by
  classical
  exact A.filter (fun v => ∃ u : V, u ∈ B ∧ G.adj u v)

theorem oldNeighbourSet_subset (A B : Finset V) :
    G.oldNeighbourSet A B ⊆ A := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem oldNeighbourSet_contains
    (A B : Finset V) {u v : V}
    (hu : u ∈ B) (hv : v ∈ A) (hAdj : G.adj u v) :
    v ∈ G.oldNeighbourSet A B := by
  classical
  exact Finset.mem_filter.mpr ⟨hv, ⟨u, hu, hAdj⟩⟩

/-- Canonical minimal old support from the strict finite d-closed hull.
All statements concern the induced graph on A∪B and its finite
subgraphs. No uniform closure bound is needed. -/
theorem canonical_dClosed_local_support
    (A B : Finset V)
    (hDisj : Disjoint A B)
    (hMin : G.toPredimension.IsMinimalDClosedStep A (A ∪ B)) :
    let N := G.oldNeighbourSet A B
    let P := G.toPredimension.dClosedHull N A
    G.toPredimension.IsDClosed P A ∧
    G.NoCrossEdges A (P ∪ B) ∧
    G.toPredimension.IsMinimalDClosedStep P (P ∪ B) ∧
    G.toPredimension.IsDClosed (P ∪ B) (A ∪ B) ∧
    G.toPredimension.dClosedHull N P = P := by
  classical
  let d := G.toPredimension
  let N := G.oldNeighbourSet A B
  let P := d.dClosedHull N A
  have hNsubA : N ⊆ A := G.oldNeighbourSet_subset A B
  have hPclosed : d.IsDClosed P A :=
    d.dClosedHull_dclosed N A
  have hPA : P ⊆ A := hPclosed.1
  have hNsubP : N ⊆ P :=
    d.subset_dClosedHull hNsubA
  have hNo : G.NoCrossEdges A (P ∪ B) := by
    apply G.noCross_of_backNeighbours A P B hPA
    intro u hu v hv hAdj
    exact hNsubP (G.oldNeighbourSet_contains A B hu hv hAdj)
  have hMinLocal : d.IsMinimalDClosedStep P (P ∪ B) :=
    (G.minimalDClosedStep_free_iff P A B hPA hDisj hNo).mpr hMin
  have hRight : d.IsDClosed (P ∪ B) (A ∪ B) :=
    G.dClosed_local_right_factor P A B hPA hDisj hNo hPclosed
  have hHull : d.dClosedHull N P = P := by
    let H := d.dClosedHull N P
    have hHclosedP : d.IsDClosed H P :=
      d.dClosedHull_dclosed N P
    have hHclosedA : d.IsDClosed H A :=
      d.dclosed_trans hHclosedP hPclosed
    have hNsubH : N ⊆ H :=
      d.subset_dClosedHull hNsubP
    have hPsubH : P ⊆ H :=
      d.dClosedHull_least hNsubH hHclosedA
    exact le_antisymm hHclosedP.1 hPsubH
  exact ⟨hPclosed, hNo, hMinLocal, hRight, hHull⟩

end GraphOn
end BigHrushovski
