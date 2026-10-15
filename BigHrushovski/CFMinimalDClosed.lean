import BigHrushovski.LocalFreeTransfer

/-!
# Minimal strict d-closed steps under local free attachment

The finite local free-extension principle is stronger than preservation
of the strict d-closedness of the endpoints: it preserves the strict
d-closedness of **every corresponding intermediate substructure**.

We formalize the exact interval correspondence, and hence the
equivalence of minimal d-closed steps under a no-cross free extension.
Neither a countable ambient graph nor a uniform closure bound is used.
-/

namespace BigHrushovski

namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- A nonempty strict d-closed extension with no proper intermediate
d-closed substructure, in the same format as IsMinimalStrongStep. -/
def IsMinimalDClosedStep (d : Predimension V)
    (a b : Finset V) : Prop :=
  d.IsDClosed a b ∧ a ≠ b ∧
    ∀ z : Finset V, a ⊆ z → z ⊆ b →
      d.IsDClosed z b → z = a ∨ z = b

end Predimension

namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The bijection between the intervals [P,P∪B] and [A,A∪B]
preserves and reflects strict d-closedness of any intermediate D.

The proof compares the relative predimensions for D and for every
later intermediate set, rather than only those of P and A. -/
theorem dClosed_intermediate_free_iff
    (P A B D : Finset V)
    (hPA : P ⊆ A)
    (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hPD : P ⊆ D) (hDE : D ⊆ P ∪ B) :
    G.toPredimension.IsDClosed D (P ∪ B) ↔
      G.toPredimension.IsDClosed (A ∪ D) (A ∪ B) := by
  have hADsub : A ∪ D ⊆ A ∪ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvA | hvD
    · exact Finset.mem_union.mpr (Or.inl hvA)
    · rcases Finset.mem_union.mp (hDE hvD) with hvP | hvB
      · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
      · exact Finset.mem_union.mpr (Or.inr hvB)
  constructor
  · intro hLocal
    refine ⟨hADsub, ?_⟩
    intro Z hADZ hZNe hZAB
    let Y : Finset V := Z ∩ (P ∪ B)
    have hDY : D ⊆ Y := by
      intro v hvD
      exact Finset.mem_inter.mpr
        ⟨hADZ (Finset.mem_union.mpr (Or.inr hvD)), hDE hvD⟩
    have hPY : P ⊆ Y := hPD.trans hDY
    have hYE : Y ⊆ P ∪ B := Finset.inter_subset_right
    have hAZ : A ⊆ Z :=
      Finset.subset_union_left.trans hADZ
    have hZeq : Z = A ∪ Y :=
      local_enlarged_intermediate_form P A B Z hPA hAZ hZAB
    have hYNe : Y ≠ D := by
      intro hEq
      apply hZNe
      calc
        Z = A ∪ Y := hZeq
        _ = A ∪ D := by rw [hEq]
    have hStrict : G.predim D < G.predim Y := by
      have h := hLocal.2 Y hDY hYNe hYE
      exact h
    have hModD := G.local_relative_predim P A B D
      hPA hDisj hNo hPD hDE
    have hModY := G.local_relative_predim P A B Y
      hPA hDisj hNo hPY hYE
    change G.predim (A ∪ D) < G.predim Z
    rw [hZeq]
    omega
  · intro hGlobal
    refine ⟨hDE, ?_⟩
    intro Y hDY hYNe hYE
    have hADY : A ∪ D ⊆ A ∪ Y := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvA | hvD
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr (hDY hvD))
    have hAYsub : A ∪ Y ⊆ A ∪ B := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvA | hvY
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · rcases Finset.mem_union.mp (hYE hvY) with hvP | hvB
        · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
        · exact Finset.mem_union.mpr (Or.inr hvB)
    have hAYNe : A ∪ Y ≠ A ∪ D := by
      intro hEq
      have hYsubD : Y ⊆ D := by
        intro v hvY
        have hv : v ∈ A ∪ D := by
          have h : v ∈ A ∪ Y :=
            Finset.mem_union.mpr (Or.inr hvY)
          rw [hEq] at h
          exact h
        rcases Finset.mem_union.mp hv with hvA | hvD
        · rcases Finset.mem_union.mp (hYE hvY) with hvP | hvB
          · exact hPD hvP
          · exact ((Finset.disjoint_left.mp hDisj) hvA hvB).elim
        · exact hvD
      exact hYNe (le_antisymm hYsubD hDY)
    have hStrict : G.predim (A ∪ D) < G.predim (A ∪ Y) := by
      have h := hGlobal.2 (A ∪ Y) hADY hAYNe hAYsub
      exact h
    have hModD := G.local_relative_predim P A B D
      hPA hDisj hNo hPD hDE
    have hModY := G.local_relative_predim P A B Y
      hPA hDisj hNo (hPD.trans hDY) hYE
    change G.predim D < G.predim Y
    omega

/-- The minimal *strict* d-closed extension, not just endpoint
d-closedness, persists and reflects under a no-cross attachment.
The old base P need not be strong or d-closed inside A. -/
theorem minimalDClosedStep_free_iff
    (P A B : Finset V)
    (hPA : P ⊆ A)
    (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B)) :
    G.toPredimension.IsMinimalDClosedStep P (P ∪ B) ↔
      G.toPredimension.IsMinimalDClosedStep A (A ∪ B) := by
  constructor
  · intro hLocal
    have hEndpoint : G.toPredimension.IsDClosed A (A ∪ B) :=
      (G.localFreeDClosed_iff P A B hPA hDisj hNo).mp hLocal.1
    refine ⟨hEndpoint, ?_, ?_⟩
    · intro hEq
      have hPB : P = P ∪ B := by
        apply le_antisymm Finset.subset_union_left
        intro v hv
        rcases Finset.mem_union.mp hv with hvP | hvB
        · exact hvP
        · have hvA : v ∈ A := by
            have h : v ∈ A ∪ B := Finset.mem_union.mpr (Or.inr hvB)
            rw [← hEq] at h
            exact h
          exact ((Finset.disjoint_left.mp hDisj) hvA hvB).elim
      exact hLocal.2.1 hPB
    · intro Z hAZ hZAB hZD
      let D : Finset V := Z ∩ (P ∪ B)
      have hPD : P ⊆ D := by
        intro v hvP
        exact Finset.mem_inter.mpr
          ⟨hAZ (hPA hvP), Finset.mem_union.mpr (Or.inl hvP)⟩
      have hDE : D ⊆ P ∪ B := Finset.inter_subset_right
      have hZeq : Z = A ∪ D :=
        local_enlarged_intermediate_form P A B Z hPA hAZ hZAB
      have hDClosed : G.toPredimension.IsDClosed D (P ∪ B) := by
        apply (G.dClosed_intermediate_free_iff P A B D
          hPA hDisj hNo hPD hDE).mpr
        rw [← hZeq]
        exact hZD
      rcases hLocal.2.2 D hPD hDE hDClosed with hEq | hEq
      · left
        have hAP : A ∪ P = A :=
          le_antisymm
            (Finset.union_subset (le_refl _) hPA)
            Finset.subset_union_left
        calc
          Z = A ∪ D := hZeq
          _ = A ∪ P := by rw [hEq]
          _ = A := hAP
      · right
        calc
          Z = A ∪ D := hZeq
          _ = A ∪ (P ∪ B) := by rw [hEq]
          _ = A ∪ B := local_old_union_eq P A B hPA
  · intro hGlobal
    have hEndpoint : G.toPredimension.IsDClosed P (P ∪ B) :=
      (G.localFreeDClosed_iff P A B hPA hDisj hNo).mpr hGlobal.1
    refine ⟨hEndpoint, ?_, ?_⟩
    · intro hEq
      have hBsubP : B ⊆ P := by
        intro v hvB
        have hv : v ∈ P ∪ B := Finset.mem_union.mpr (Or.inr hvB)
        rw [← hEq] at hv
        exact hv
      have hAeq : A = A ∪ B :=
        le_antisymm Finset.subset_union_left
          (Finset.union_subset (le_refl _) (hBsubP.trans hPA))
      exact hGlobal.2.1 hAeq
    · intro D hPD hDE hDClosed
      have hADClosed : G.toPredimension.IsDClosed
          (A ∪ D) (A ∪ B) :=
        (G.dClosed_intermediate_free_iff P A B D
          hPA hDisj hNo hPD hDE).mp hDClosed
      have hADSub : A ∪ D ⊆ A ∪ B := by
        intro v hv
        rcases Finset.mem_union.mp hv with hvA | hvD
        · exact Finset.mem_union.mpr (Or.inl hvA)
        · rcases Finset.mem_union.mp (hDE hvD) with hvP | hvB
          · exact Finset.mem_union.mpr (Or.inl (hPA hvP))
          · exact Finset.mem_union.mpr (Or.inr hvB)
      rcases hGlobal.2.2 (A ∪ D) Finset.subset_union_left
          hADSub hADClosed with hEq | hEq
      · left
        have hDsubA : D ⊆ A := by
          intro v hvD
          have hv : v ∈ A ∪ D :=
            Finset.mem_union.mpr (Or.inr hvD)
          rw [hEq] at hv
          exact hv
        have hDsubP : D ⊆ P := by
          intro v hvD
          rcases Finset.mem_union.mp (hDE hvD) with hvP | hvB
          · exact hvP
          · exact ((Finset.disjoint_left.mp hDisj)
            (hDsubA hvD) hvB).elim
        exact le_antisymm hDsubP hPD
      · right
        have hBsubD : B ⊆ D := by
          intro v hvB
          have hv : v ∈ A ∪ B :=
            Finset.mem_union.mpr (Or.inr hvB)
          rw [← hEq] at hv
          rcases Finset.mem_union.mp hv with hvA | hvD
          · exact ((Finset.disjoint_left.mp hDisj) hvA hvB).elim
          · exact hvD
        exact le_antisymm hDE (Finset.union_subset hPD hBsubD)

end GraphOn
end BigHrushovski
