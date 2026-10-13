import BigHrushovski.C0UnaryClosedStrong
import BigHrushovski.FiniteDecomposition

/-!
# Local minimality in a no-cross free amalgam

Suppose P is contained in an old finite graph A, B is a disjoint new
block, and there is no edge from B to A \ P. Every intermediate D with
P ⊆ D ⊆ P ∪ B then satisfies the exact relative predimension identity

  δ(A ∪ D) + δ(P) = δ(A) + δ(D).

This identity transfers self-sufficiency and minimality of strong steps
from the enlarged old prefix A to the smaller lower closure P.

All edges are unordered. Neither an ordering of B nor a named
temporary generator occurs in the hypotheses.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Every intermediate local extension D has exactly P as its
intersection with the larger old vertex set A. -/
theorem local_inter_eq (P A B D : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hPD : P ⊆ D) (hDB : D ⊆ P ∪ B) :
    A ∩ D = P := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvA, hvD⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp (hDB hvD) with hvP | hvB
    · exact hvP
    · exact ((Finset.disjoint_left.mp hDisj) hvA hvB).elim
  · intro hv
    exact Finset.mem_inter.mpr ⟨hPA hv, hPD hv⟩

/-- Predimension is modular over P for *all* local intermediate sets,
not only at the endpoint of the free amalgam. -/
theorem local_relative_predim (P A B D : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hPD : P ⊆ D) (hDB : D ⊆ P ∪ B) :
    G.predim (A ∪ D) + G.predim P =
      G.predim A + G.predim D := by
  have hPB : P ⊆ P ∪ B := Finset.subset_union_left
  have hRefl : P ∪ B ⊆ P ∪ B := le_refl _
  have hOverlap : A ∩ (P ∪ B) = P :=
    G.local_inter_eq P A B (P ∪ B) hPA hDisj hPB hRefl
  have hBase : A ∩ (P ∪ B) ⊆ D := by
    rw [hOverlap]
    exact hPD
  have hNoD : G.NoCrossEdges A D :=
    G.noCross_restrict_right A (P ∪ B) D hNo hDB hBase
  have hDelta := G.predim_modular_of_noCross A D hNoD
  rw [G.local_inter_eq P A B D hPA hDisj hPD hDB] at hDelta
  exact hDelta

/-- The global minimal-step strongness inequality implies the
self-sufficiency of the smaller local base P in P ∪ B. -/
theorem local_strong_of_enlarged_strong (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hStrong : G.toPredimension.IsStrong A (A ∪ B)) :
    G.toPredimension.IsStrong P (P ∪ B) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro D hPD hDB
  have hAUB : A ∪ D ⊆ A ∪ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvD
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp (hDB hvD) with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  have hAstrong : G.predim A ≤ G.predim (A ∪ D) := by
    have h := hStrong.2 (A ∪ D) Finset.subset_union_left hAUB
    change G.predim A ≤ G.predim (A ∪ D) at h
    exact h
  have hDelta := G.local_relative_predim P A B D
    hPA hDisj hNo hPD hDB
  change G.predim P ≤ G.predim D
  omega

/-- A local strong intermediate set D remains strong after adjoining
the larger old graph A without crossing edges. -/
theorem local_strong_lift (P A B D : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hPD : P ⊆ D) (hDB : D ⊆ P ∪ B)
    (hStrong : G.toPredimension.IsStrong D (P ∪ B)) :
    G.toPredimension.IsStrong (A ∪ D) (A ∪ B) := by
  have hAUB : A ∪ D ⊆ A ∪ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvD
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp (hDB hvD) with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  refine ⟨hAUB, ?_⟩
  intro C hADC hCAB
  let E : Finset V := C ∩ (P ∪ B)
  have hPE : P ⊆ E := by
    intro v hv
    have hvA : v ∈ A := hPA hv
    have hvC : v ∈ C :=
      hADC (Finset.mem_union.mpr (Or.inl hvA))
    exact Finset.mem_inter.mpr
      ⟨hvC, Finset.mem_union.mpr (Or.inl hv)⟩
  have hDE : D ⊆ E := by
    intro v hv
    exact Finset.mem_inter.mpr
      ⟨hADC (Finset.mem_union.mpr (Or.inr hv)), hDB hv⟩
  have hEPB : E ⊆ P ∪ B := Finset.inter_subset_right
  have hEq : C = A ∪ E := by
    ext v
    constructor
    · intro hvC
      rcases Finset.mem_union.mp (hCAB hvC) with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr
            ⟨hvC, Finset.mem_union.mpr (Or.inr hvB)⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvE
      · exact hADC (Finset.mem_union.mpr (Or.inl hvA))
      · exact (Finset.mem_inter.mp hvE).1
  have hLocal : G.predim D ≤ G.predim E := by
    have h := hStrong.2 E hDE hEPB
    change G.predim D ≤ G.predim E at h
    exact h
  have hDDelta := G.local_relative_predim P A B D
    hPA hDisj hNo hPD hDB
  have hEDelta := G.local_relative_predim P A B E
    hPA hDisj hNo hPE hEPB
  change G.predim (A ∪ D) ≤ G.predim C
  rw [hEq]
  omega

/-- Minimality of the strong step A ⊂ A ∪ B descends to the
local lower closure P ⊂ P ∪ B when all old neighbours of B lie in P. -/
theorem minimalStrongStep_local_of_noCross
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hMin : G.toPredimension.IsMinimalStrongStep A (A ∪ B)) :
    G.toPredimension.IsMinimalStrongStep P (P ∪ B) := by
  have hStrong : G.toPredimension.IsStrong P (P ∪ B) :=
    G.local_strong_of_enlarged_strong P A B hPA hDisj hNo hMin.1
  refine ⟨hStrong, ?_, ?_⟩
  · intro hEq
    have hBsubA : B ⊆ A := by
      intro v hvB
      have hvPB : v ∈ P ∪ B :=
        Finset.mem_union.mpr (Or.inr hvB)
      rw [← hEq] at hvPB
      exact hPA hvPB
    have hAeq : A = A ∪ B :=
      le_antisymm Finset.subset_union_left
        (Finset.union_subset (Subset.rfl) hBsubA)
    exact hMin.2.1 hAeq
  · intro D hPD hDB hDstrong
    have hLift : G.toPredimension.IsStrong (A ∪ D) (A ∪ B) :=
      G.local_strong_lift P A B D
        hPA hDisj hNo hPD hDB hDstrong
    have hAUB : A ∪ D ⊆ A ∪ B := hLift.1
    rcases hMin.2.2 (A ∪ D) Finset.subset_union_left hAUB
      hLift with hCase | hCase
    · left
      have hDA : D ⊆ A := by
        intro v hv
        have hvUnion : v ∈ A ∪ D :=
          Finset.mem_union.mpr (Or.inr hv)
        rw [hCase] at hvUnion
        exact hvUnion
      have hDP : D ⊆ P := by
        intro v hv
        rcases Finset.mem_union.mp (hDB hv) with hvP | hvB
        · exact hvP
        · exact ((Finset.disjoint_left.mp hDisj) (hDA hv) hvB).elim
      exact le_antisymm hDP hPD
    · right
      have hBsubD : B ⊆ D := by
        intro v hvB
        have hvUnion : v ∈ A ∪ B :=
          Finset.mem_union.mpr (Or.inr hvB)
        rw [← hCase] at hvUnion
        rcases Finset.mem_union.mp hvUnion with hvA | hvD
        · exact ((Finset.disjoint_left.mp hDisj) hvA hvB).elim
        · exact hvD
      exact le_antisymm hDB (Finset.union_subset hPD hBsubD)

end GraphOn
end BigHrushovski
