import BigHrushovski.C0LocalFreeConverse

/-!
# Strict d-closed factors of a free graph amalgam

For finite vertex sets A and E with no edges between A\E and E\A,
the strict d-closedness of their intersection in A implies the
strict d-closedness of the entire factor E in A∪E.

This is the strict version of strong_right_of_noCross and is a
separate requirement from minimal-d-closed-step transport. It is
used to justify both d-closed factors in the C_F local-support lemma.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- The left free-amalgamation factor is strictly d-closed provided
the intersection is d-closed in the other factor. -/
theorem dClosed_left_of_noCross
    (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hBase : G.toPredimension.IsDClosed (a ∩ b) b) :
    G.toPredimension.IsDClosed a (a ∪ b) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro x hax hxNe hxab
  let c : Finset V := x ∩ b
  have hcb : c ⊆ b := Finset.inter_subset_right
  have hPsub : a ∩ b ⊆ c := by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hva, hvb⟩
    exact Finset.mem_inter.mpr ⟨hax hva, hvb⟩
  have hXeq : x = a ∪ c := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp (hxab hv) with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hv, hvB⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvC
      · exact hax hvA
      · exact (Finset.mem_inter.mp hvC).1
  have hPcap : a ∩ c = a ∩ b := by
    apply le_antisymm
    · intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hva, hvc⟩
      exact Finset.mem_inter.mpr ⟨hva, hcb hvc⟩
    · intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1, hPsub hv⟩
  have hNoC : G.NoCrossEdges a c :=
    G.noCross_restrict_right a b c hNo hcb hPsub
  have hCNe : c ≠ a ∩ b := by
    intro hEq
    apply hxNe
    calc
      x = a ∪ c := hXeq
      _ = a ∪ (a ∩ b) := by rw [hEq]
      _ = a := le_antisymm
        (Finset.union_subset (le_refl _) Finset.inter_subset_left)
        Finset.subset_union_left
  have hStrict : G.predim (a ∩ b) < G.predim c := by
    have h := hBase.2 c hPsub hCNe hcb
    exact h
  have hMod := G.predim_modular_of_noCross a c hNoC
  rw [hPcap] at hMod
  change G.predim a < G.predim x
  rw [hXeq]
  omega

/-- Symmetric version: the right factor is d-closed whenever the
intersection is d-closed in the left factor. -/
theorem dClosed_right_of_noCross
    (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hBase : G.toPredimension.IsDClosed (a ∩ b) a) :
    G.toPredimension.IsDClosed b (a ∪ b) := by
  have hSwap : G.NoCrossEdges b a := by
    intro e he
    have heAB : e ∈ G.edgesWithin (a ∪ b) := by
      simpa only [Finset.union_comm] using he
    rcases Finset.mem_union.mp (hNo heAB) with heA | heB
    · exact Finset.mem_union.mpr (Or.inr heA)
    · exact Finset.mem_union.mpr (Or.inl heB)
  have hP' : G.toPredimension.IsDClosed (b ∩ a) a := by
    simpa only [Finset.inter_comm] using hBase
  simpa only [Finset.union_comm] using
    (G.dClosed_left_of_noCross b a hSwap hP')

/-- In the local-support notation, strict closure P≤d A makes
E=P∪B a d-closed factor of the free graph amalgam A∪B. This
is independent of the local minimal-step hypotheses. -/
theorem dClosed_local_right_factor
    (P A B : Finset V)
    (hPA : P ⊆ A) (hDisj : Disjoint A B)
    (hNo : G.NoCrossEdges A (P ∪ B))
    (hBase : G.toPredimension.IsDClosed P A) :
    G.toPredimension.IsDClosed (P ∪ B) (A ∪ B) := by
  have hIntersect : A ∩ (P ∪ B) = P :=
    local_inter_eq P A B (P ∪ B)
      hPA hDisj Finset.subset_union_left (le_refl _)
  have hBase' : G.toPredimension.IsDClosed
      (A ∩ (P ∪ B)) A := by
    rw [hIntersect]
    exact hBase
  have hFactor :=
    G.dClosed_right_of_noCross A (P ∪ B) hNo hBase'
  rw [local_old_union_eq P A B hPA] at hFactor
  exact hFactor

end GraphOn
end BigHrushovski
