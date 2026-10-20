import BigHrushovski.CFBirthLocalRoots
import BigHrushovski.CFBatchDClosed
import BigHrushovski.CFLocalSupportTransport

/-!
# Recover the old support of a literal C_F birth block

An actual tagged birth block B has a literally named old support P.
We show that P is globally strictly d-closed in the countable graph
and is generated there by exactly its old vertices adjacent to B.

The proof transports the previously verified local exact-support
certificate through the induced birth embedding. It then compares
the finite d-closed hull inside P with the least globally d-closed
hull. This supplies the graph-theoretic support reconstruction
needed to prove that the (R,H)-presentation preserves all b-values.

No language with partial functions or big Ramsey theorem is used.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The actual old neighbours of a request's fresh block, among
the vertices of its named old support. -/
noncomputable def birthSupportNeighbours
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) : Finset (Vertex F K) := by
  classical
  exact (countableGraph F K).oldNeighbourSet
    (birthSupport F K n r) (birthBlock F K n r)

/-- The named support of every literal birth block is globally
strictly d-closed, not merely closed inside its preceding stage. -/
theorem birthSupport_global_dClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) :
    (countableGraph F K).toPredimension.IsGloballyDClosed
      (birthSupport F K n r) := by
  classical
  let G := (stage F K n).graph
  let Allowed : AllowedLocal (stage F K n).carrier :=
    GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  have hClosed :
      (stage F K (n + 1)).graph.toPredimension.IsDClosed
        (taggedSupport G Allowed bound r) Finset.univ :=
    taggedSupport_dClosed_full G Allowed bound r
  exact finiteClosedPart_global F K (n + 1)
    (taggedSupport G Allowed bound r) hClosed

/-- The exact old-neighbour certificate from the finite local
graph transports without loss of any edge or nonedge to the
countable birth-labelled graph. The hull here is computed
inside the literal named support. -/
theorem birthSupport_eq_finiteHull_neighbours
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) :
    (countableGraph F K).toPredimension.dClosedHull
      (birthSupportNeighbours F K n r)
      (birthSupport F K n r) =
        birthSupport F K n r := by
  classical
  let G := (stage F K n).graph
  let Allowed : AllowedLocal (stage F K n).carrier :=
    GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun P => K P.card
  let H := (stage F K (n + 1)).graph
  let f := toVertex F K (n + 1)
  let P := taggedSupport G Allowed bound r
  let B := taggedBlock G Allowed bound r
  have hAdj : ∀ u v : (stage F K (n + 1)).carrier,
      H.adj u v ↔ (countableGraph F K).adj (f u) (f v) := by
    intro u v
    exact (countableGraph_stage_induced F K (n + 1) u v).symm
  have hNat := H.canonicalOldSupport_image
    (countableGraph F K) f (toVertex_injective F K (n + 1))
    hAdj P B
  have hExact : H.toPredimension.dClosedHull
      (H.oldNeighbourSet P B) P = P :=
    taggedLocal_exactSupport G Allowed bound r
  rw [hExact] at hNat
  exact hNat.symm

/-- The support is in fact the least globally strictly d-closed
hull of the finite set of its actual old neighbours of the
fresh request block. No separate choice of a finite ambient
stage or a support is involved in this equation. -/
theorem birthSupport_eq_globalHull_neighbours
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r : BirthRequest F K n) :
    birthDClosedHull F K (birthSupportNeighbours F K n r) =
      birthSupport F K n r := by
  let d := (countableGraph F K).toPredimension
  let P := birthSupport F K n r
  let N := birthSupportNeighbours F K n r
  have hNP : N ⊆ P :=
    (countableGraph F K).oldNeighbourSet_subset P
      (birthBlock F K n r)
  have hPGlobal : d.IsGloballyDClosed P :=
    birthSupport_global_dClosed F K n r
  have hHullP : birthDClosedHull F K N ⊆ P :=
    d.globalDClosedHull_least (birthDClosedChain F K) hNP hPGlobal
  have hHullGlobal : d.IsGloballyDClosed (birthDClosedHull F K N) :=
    birthDClosedHull_global F K N
  have hRelative : d.IsDClosed (birthDClosedHull F K N) P :=
    Predimension.IsGloballyDClosed.restrict d hHullGlobal hHullP
  have hNInHull : N ⊆ birthDClosedHull F K N :=
    d.subset_globalDClosedHull (birthDClosedChain F K) N
  have hPHull : P ⊆ birthDClosedHull F K N := by
    have hExact : d.dClosedHull N P = P :=
      birthSupport_eq_finiteHull_neighbours F K n r
    rw [← hExact]
    exact d.dClosedHull_least hNInHull hRelative
  exact le_antisymm hHullP hPHull

end CFCoherentTower
end BigHrushovski
