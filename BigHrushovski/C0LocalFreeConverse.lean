import BigHrushovski.C0LocalFreeMinimal

/-!
# Persistence of a local minimal strong step under free amalgamation

Let P⊆A, with a new block B disjoint from A and no edges joining B
to A\P. The relative predimension equality established in
C0LocalFreeMinimal transfers *all* strong intermediates in both
directions. Hence P⊂P∪B is minimal strong if and only if
A⊂A∪B is minimal strong.

This proves the finite free-amalgamation persistence clause of the
C0 local-form lemma. It does not require that the old set A be
globally strong and does not assert the functional Fraisse extension
property.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Every enlarged intermediate has the form A ∪ D, where
D is its restriction to the local extension P ∪ B. -/
theorem local_enlarged_intermediate_form
    (P A B Z : Finset V)
    (hPA : P ⊆ A) (hAZ : A ⊆ Z) (hZAB : Z ⊆ A ∪ B) :
    Z = A ∪ (Z ∩ (P ∪ B)) := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp (hZAB hv) with hvA | hvB
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_inter.mpr
          ⟨hv, Finset.mem_union.mpr (Or.inr hvB)⟩))
  · intro hv
    rcases Finset.mem_union.mp hv with hvA | hvZ
    · exact hAZ hvA
    · exact (Finset.mem_inter.mp hvZ).1

theorem local_old_union_eq (P A B : Finset V)
    (hPA : P ⊆ A) :
    A ∪ (P ∪ B) = A ∪ B := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hvA | hvPB
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp hvPB with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  · intro hv
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inr hvB)))

/-- A strong local base P in P∪B remains strong after adjoining
the larger old set A, using the verified local strong lift. -/
theorem enlarged_strong_of_local_strong
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hStrong : G.toPredimension.IsStrong P (P ∪ B)) :
    G.toPredimension.IsStrong A (A ∪ B) := by
  have hLift := G.local_strong_lift P A B P
    hPA hDisj hNo (le_refl _) Finset.subset_union_left hStrong
  have hEq : A ∪ P = A := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvP
      · exact hvA
      · exact hPA hvP
    · intro hv
      exact Finset.mem_union.mpr (Or.inl hv)
  rw [hEq] at hLift
  exact hLift

/-- The reverse restriction of the strongness comparison:
any enlarged strong intermediate Z restricts to a local strong
intermediate Z∩(P∪B). -/
theorem local_strong_restrict_of_enlarged
    (P A B Z : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hAZ : A ⊆ Z)
    (hStrong : G.toPredimension.IsStrong Z (A ∪ B)) :
    G.toPredimension.IsStrong (Z ∩ (P ∪ B)) (P ∪ B) := by
  let D : Finset V := Z ∩ (P ∪ B)
  have hPD : P ⊆ D := by
    intro v hvP
    exact Finset.mem_inter.mpr
      ⟨hAZ (hPA hvP), Finset.mem_union.mpr (Or.inl hvP)⟩
  have hDPB : D ⊆ P ∪ B := Finset.inter_subset_right
  have hZeq : Z = A ∪ D :=
    G.local_enlarged_intermediate_form P A B Z
      hPA hAZ hStrong.1
  refine ⟨hDPB, ?_⟩
  intro E hDE hEPB
  have hPE : P ⊆ E := hPD.trans hDE
  have hAEAB : A ∪ E ⊆ A ∪ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvE
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp (hEPB hvE) with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  have hZAE : Z ⊆ A ∪ E := by
    intro v hv
    have hvU : v ∈ A ∪ D := by
      rw [← hZeq]
      exact hv
    rcases Finset.mem_union.mp hvU with hvA | hvD
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · exact Finset.mem_union.mpr (Or.inr (hDE hvD))
  have hStrongZ : G.predim (A ∪ D) ≤ G.predim (A ∪ E) := by
    have hh := hStrong.2 (A ∪ E) hZAE hAEAB
    change G.predim Z ≤ G.predim (A ∪ E) at hh
    rw [hZeq] at hh
    exact hh
  have hDdelta := G.local_relative_predim P A B D
    hPA hDisj hNo hPD hDPB
  have hEdelta := G.local_relative_predim P A B E
    hPA hDisj hNo hPE hEPB
  change G.predim D ≤ G.predim E
  omega

/-- Attaching an old graph freely over P preserves a local
minimal strong extension with new block B. -/
theorem minimalStrongStep_enlarged_of_local
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hMin : G.toPredimension.IsMinimalStrongStep P (P ∪ B)) :
    G.toPredimension.IsMinimalStrongStep A (A ∪ B) := by
  have hStrong : G.toPredimension.IsStrong A (A ∪ B) :=
    G.enlarged_strong_of_local_strong P A B hPA hDisj hNo hMin.1
  refine ⟨hStrong, ?_, ?_⟩
  · intro hEq
    have hBsubA : B ⊆ A := by
      intro v hvB
      have hv : v ∈ A ∪ B := Finset.mem_union.mpr (Or.inr hvB)
      rw [← hEq] at hv
      exact hv
    have hPBsubsetP : P ∪ B ⊆ P := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvP | hvB
      · exact hvP
      · exact ((Finset.disjoint_left.mp hDisj) (hBsubA hvB) hvB).elim
    exact hMin.2.1
      (le_antisymm Finset.subset_union_left hPBsubsetP)
  · intro Z hAZ hZAB hZstrong
    let D : Finset V := Z ∩ (P ∪ B)
    have hDstrong : G.toPredimension.IsStrong D (P ∪ B) :=
      G.local_strong_restrict_of_enlarged P A B Z
        hPA hDisj hNo hAZ hZstrong
    have hZeq : Z = A ∪ D :=
      G.local_enlarged_intermediate_form P A B Z
        hPA hAZ hZAB
    have hAP : A ∪ P = A := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_union.mp hv with hvA | hvP
        · exact hvA
        · exact hPA hvP
      · intro hv
        exact Finset.mem_union.mpr (Or.inl hv)
    have hPD : P ⊆ D := by
      intro v hvP
      exact Finset.mem_inter.mpr
        ⟨hAZ (hPA hvP), Finset.mem_union.mpr (Or.inl hvP)⟩
    rcases hMin.2.2 D hPD hDstrong.1 hDstrong with hDP | hDfull
    · left
      calc
        Z = A ∪ D := hZeq
        _ = A ∪ P := by rw [hDP]
        _ = A := hAP
    · right
      calc
        Z = A ∪ D := hZeq
        _ = A ∪ (P ∪ B) := by rw [hDfull]
        _ = A ∪ B := G.local_old_union_eq P A B hPA

/-- Local minimality and its freely amalgamated extension are
equivalent under the exact no-cross and disjointness hypotheses. -/
theorem minimalStrongStep_free_iff
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B)) :
    G.toPredimension.IsMinimalStrongStep P (P ∪ B) ↔
      G.toPredimension.IsMinimalStrongStep A (A ∪ B) := by
  constructor
  · exact G.minimalStrongStep_enlarged_of_local P A B hPA hDisj hNo
  · exact G.minimalStrongStep_local_of_noCross P A B hPA hDisj hNo

end GraphOn
end BigHrushovski
