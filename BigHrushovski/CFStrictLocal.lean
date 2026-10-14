import BigHrushovski.C0LocalFreeMinimal

/-!
# Strict predimension closure under a local no-cross amalgam

Let P be contained in an old finite vertex set A, and let B be a
disjoint new block with no edges to A\P. For every intermediate
P ⊆ D ⊆ P∪B, the finite predimension is modular over P.

The local-relative-predimension identity already proved for the
C0 construction therefore transfers the *strict* d-closed condition
between P <=_d P∪B and A <=_d A∪B.

These are the numerical interfaces for the C_F minimal local-support
lemma. Full minimality of d-closed steps and the global C_F level
construction remain separate obligations.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- A strict d-closed extension over the larger old base descends to the
smaller local support when no new vertex meets the omitted old part. -/
theorem dClosed_local_of_noCross
    (P A B : Finset V)
    (hPA : P ⊆ A)
    (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hGlobal : G.toPredimension.IsDClosed A (A ∪ B)) :
    G.toPredimension.IsDClosed P (P ∪ B) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro D hPD hDNe hDB
  have hAUB : A ∪ D ⊆ A ∪ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvD
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp (hDB hvD) with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  have hAUNe : A ∪ D ≠ A := by
    intro hEq
    have hDsubA : D ⊆ A := by
      intro v hvD
      have hv : v ∈ A ∪ D := Finset.mem_union.mpr (Or.inr hvD)
      rw [hEq] at hv
      exact hv
    have hDsubP : D ⊆ P := by
      intro v hvD
      rcases Finset.mem_union.mp (hDB hvD) with hvP | hvB
      · exact hvP
      · exact ((Finset.disjoint_left.mp hDisj) (hDsubA hvD) hvB).elim
    exact hDNe (le_antisymm hDsubP hPD)
  have hStrict : G.predim A < G.predim (A ∪ D) := by
    have h := hGlobal.2 (A ∪ D)
      Finset.subset_union_left hAUNe hAUB
    exact h
  have hMod := G.local_relative_predim P A B D
    hPA hDisj hNo hPD hDB
  change G.predim P < G.predim D
  omega

/-- Conversely, strict d-closedness over the local support persists
after adjoining a larger old graph freely over that support. -/
theorem dClosed_enlarged_of_noCross
    (P A B : Finset V)
    (hPA : P ⊆ A)
    (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hLocal : G.toPredimension.IsDClosed P (P ∪ B)) :
    G.toPredimension.IsDClosed A (A ∪ B) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro Y hAY hYNe hYAB
  let D : Finset V := Y ∩ (P ∪ B)
  have hPD : P ⊆ D := by
    intro v hvP
    exact Finset.mem_inter.mpr
      ⟨hAY (hPA hvP), Finset.mem_union.mpr (Or.inl hvP)⟩
  have hDB : D ⊆ P ∪ B := Finset.inter_subset_right
  have hYeq : Y = A ∪ D := by
    ext v
    constructor
    · intro hvY
      rcases Finset.mem_union.mp (hYAB hvY) with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr
            ⟨hvY, Finset.mem_union.mpr (Or.inr hvB)⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvD
      · exact hAY hvA
      · exact (Finset.mem_inter.mp hvD).1
  have hDNe : D ≠ P := by
    intro hEq
    have hEqA : Y = A := by
      rw [hYeq, hEq]
      exact le_antisymm
        (Finset.union_subset (le_refl _) hPA)
        Finset.subset_union_left
    exact hYNe hEqA
  have hStrict : G.predim P < G.predim D := by
    have h := hLocal.2 D hPD hDNe hDB
    exact h
  have hMod := G.local_relative_predim P A B D
    hPA hDisj hNo hPD hDB
  change G.predim A < G.predim Y
  rw [hYeq]
  omega

end GraphOn
end BigHrushovski
