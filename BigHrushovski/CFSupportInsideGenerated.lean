import BigHrushovski.CFBirthTopBlock
import BigHrushovski.CFBirthOldNeighbours
import BigHrushovski.GlobalDClosedHull

/-!
# Intrinsic support recovery inside a generated C_F closure

For an actual vertex v of a request-tagged fresh block B, the finite
b-generated closure C(v) has B as its unique top birth-level block.
Its complement C(v)\B consists entirely of earlier vertices, including
the full literal named support P of B.

The no-cross boundary theorem identifies the neighbours of B inside
C(v)\B with its old neighbours inside P. Since C(v) is globally
strictly d-closed and the old neighbours globally generate P,
we recover P by the finite d-closure computed in the induced
graph on C(v).

This is the precise support formula used in the manuscript to
transport complete auxiliary b-values under induced embeddings of
the (R,H)-presentation. No assumptions about arbitrary infinite
predimensions, free amalgamation, or additional vertex names enter.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- The complete old named support of B is recovered from the induced
graph on the finite generated closure C(v). In this formula B is
the literal block of v, independently recoverable as the top-level
part of C(v), and C(v)\B contains exactly the earlier blocks.

The generating neighbours are taken from the *whole* C(v)\B, not
just the named support; the exact no-cross theorem shows these
sets of neighbours coincide. -/
theorem birthSupport_eq_hull_inside_generated
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val) :
    (countableGraph F K).toPredimension.dClosedHull
      ((countableGraph F K).oldNeighbourSet
        (birthGeneratedClosure F K
            ({(⟨n, ⟨r, i⟩⟩ : Vertex F K)} : Finset (Vertex F K)) \
          birthBlock F K n r)
        (birthBlock F K n r))
      (birthGeneratedClosure F K
        ({(⟨n, ⟨r, i⟩⟩ : Vertex F K)} : Finset (Vertex F K))) =
      birthSupport F K n r := by
  classical
  let G := countableGraph F K
  let d := G.toPredimension
  let v : Vertex F K := ⟨n, ⟨r, i⟩⟩
  let C := birthGeneratedClosure F K ({v} : Finset (Vertex F K))
  let P := birthSupport F K n r
  let B := birthBlock F K n r
  let old := birthGeneratedClosure F K P
  let N := birthSupportNeighbours F K n r
  have hDecomp : C = old ∪ B :=
    birthGeneratedClosure_fresh_decompose F K n r i
  have hOldStage : old ⊆ stageImage F K n :=
    birthGeneratedSupport_subset_stageImage F K n r
  have hPsubsetC : P ⊆ C := by
    intro w hw
    rw [hDecomp]
    apply Finset.mem_union.mpr
    exact Or.inl ((birthGeneratedClosure_contains F K P) hw)
  have hPsubsetEarlier : P ⊆ C \ B := by
    intro w hw
    apply Finset.mem_sdiff.mpr
    constructor
    · exact hPsubsetC hw
    · intro hwB
      have hLt : w.1 < n := birthSupport_birth_lt F K n r hw
      have hEq : w.1 = n := birthBlock_birth_eq F K n r hwB
      exact (Nat.ne_of_lt hLt) hEq
  have hEarlierSubsetStage : C \ B ⊆ stageImage F K n := by
    intro w hw
    have hwC : w ∈ C := (Finset.mem_sdiff.mp hw).1
    have hwNotB : w ∉ B := (Finset.mem_sdiff.mp hw).2
    rw [hDecomp] at hwC
    rcases Finset.mem_union.mp hwC with hOld | hB
    · exact hOldStage hOld
    · exact False.elim (hwNotB hB)
  have hNeighbours :
      G.oldNeighbourSet (C \ B) B = N :=
    birthOldNeighbours_eq_within_old F K n r
      (C \ B) hPsubsetEarlier hEarlierSubsetStage
  have hCClosed : IsBirthBlockClosed F K C :=
    birthGeneratedClosure_closed F K ({v})
  have hCGlobal : d.IsGloballyDClosed C :=
    birthBlockClosed_global_dClosed F K C hCClosed
  have hNsubsetP : N ⊆ P :=
    G.oldNeighbourSet_subset P B
  have hNsubsetC : N ⊆ C :=
    hNsubsetP.trans hPsubsetC
  have hContainer :
      birthDClosedHull F K N = d.dClosedHull N C :=
    d.globalDClosedHull_eq_closedContainer
      (birthDClosedChain F K) N C hNsubsetC hCGlobal
  calc
    d.dClosedHull (G.oldNeighbourSet (C \ B) B) C =
        d.dClosedHull N C := by rw [hNeighbours]
    _ = birthDClosedHull F K N := hContainer.symm
    _ = P := birthSupport_eq_globalHull_neighbours F K n r

end CFCoherentTower
end BigHrushovski
