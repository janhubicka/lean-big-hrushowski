import BigHrushovski.FreeAmalgam

/-!
# Preservation of 2-sparsity across free graph unions

The 2-sparse class C0 consists of finite graphs in which every induced
finite vertex subset has nonnegative predimension.

A no-crossing union preserves 2-sparsity when one factor is 2-sparse
and the intersection is strong in the other factor. The proof uses the
modular predimension calculation and the standard intersection inequality
for self-sufficient substructures.

This is a structural lemma needed for strong free amalgamation. It is
not a construction of all amalgams or of the Fraisse limit.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- A finite induced graph is 2-sparse when every finite induced
subgraph has nonnegative predimension. -/
def IsTwoSparse (a : Finset V) : Prop :=
  ∀ s : Finset V, s ⊆ a → 0 ≤ G.predim s

/-- A strong extension of a 2-sparse finite substructure remains
2-sparse, since every finite subset has predimension at least that
of its intersection with the strong base. -/
theorem twoSparse_of_strong_extension {a b : Finset V}
    (ha : G.IsTwoSparse a)
    (hab : G.toPredimension.IsStrong a b) :
    G.IsTwoSparse b := by
  intro s hsb
  have hBase : G.predim (a ∩ s) ≤ G.predim s := by
    have h := G.toPredimension.delta_inter_le_of_strong hab hsb
    change G.predim (a ∩ s) ≤ G.predim s at h
    exact h
  have hNonneg : 0 ≤ G.predim (a ∩ s) :=
    ha (a ∩ s) Finset.inter_subset_left
  omega

/-- If A and B have no crossing edges, their intersections with the
same finite subset also have no crossing edges. -/
theorem noCross_inter (a b x : Finset V)
    (hNo : G.NoCrossEdges a b) :
    G.NoCrossEdges (a ∩ x) (b ∩ x) := by
  intro edge he
  obtain ⟨hSub, hEdge⟩ :=
    (G.mem_edgesWithin_iff ((a ∩ x) ∪ (b ∩ x)) edge).mp he
  have hAB : edge ⊆ a ∪ b := by
    intro v hv
    rcases Finset.mem_union.mp (hSub hv) with hAX | hBX
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mp hAX).1)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_inter.mp hBX).1)
  have hX : edge ⊆ x := by
    intro v hv
    rcases Finset.mem_union.mp (hSub hv) with hAX | hBX
    · exact (Finset.mem_inter.mp hAX).2
    · exact (Finset.mem_inter.mp hBX).2
  have heAB : edge ∈ G.edgesWithin (a ∪ b) :=
    (G.mem_edgesWithin_iff (a ∪ b) edge).mpr ⟨hAB, hEdge⟩
  rcases Finset.mem_union.mp (hNo heAB) with heA | heB
  · have hA : edge ⊆ a :=
      ((G.mem_edgesWithin_iff a edge).mp heA).1
    have hAX : edge ⊆ a ∩ x := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hA hv, hX hv⟩
    exact Finset.mem_union.mpr (Or.inl
      ((G.mem_edgesWithin_iff (a ∩ x) edge).mpr ⟨hAX, hEdge⟩))
  · have hB : edge ⊆ b :=
      ((G.mem_edgesWithin_iff b edge).mp heB).1
    have hBX : edge ⊆ b ∩ x := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hB hv, hX hv⟩
    exact Finset.mem_union.mpr (Or.inr
      ((G.mem_edgesWithin_iff (b ∩ x) edge).mpr ⟨hBX, hEdge⟩))

/-- Free joining a 2-sparse factor A over a base strong in B preserves
2-sparsity of the entire union. -/
theorem twoSparse_union_of_noCross (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hSparseA : G.IsTwoSparse a)
    (hP : G.toPredimension.IsStrong (a ∩ b) b) :
    G.IsTwoSparse (a ∪ b) := by
  intro x hx
  have hSplit : x = (a ∩ x) ∪ (b ∩ x) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp (hx hv) with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hvA, hv⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hvB, hv⟩))
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · exact (Finset.mem_inter.mp hvA).2
      · exact (Finset.mem_inter.mp hvB).2
  have hNoX : G.NoCrossEdges (a ∩ x) (b ∩ x) :=
    G.noCross_inter a b x hNo
  have hMod := G.predim_modular_of_noCross (a ∩ x) (b ∩ x) hNoX
  have hRight : b ∩ x ⊆ b := Finset.inter_subset_left
  have hBase : G.predim ((a ∩ b) ∩ (b ∩ x)) ≤ G.predim (b ∩ x) := by
    have h := G.toPredimension.delta_inter_le_of_strong hP hRight
    change G.predim ((a ∩ b) ∩ (b ∩ x)) ≤
      G.predim (b ∩ x) at h
    exact h
  have hMeet :
      (a ∩ b) ∩ (b ∩ x) = (a ∩ x) ∩ (b ∩ x) := by
    ext v
    simp only [Finset.mem_inter]
    tauto
  rw [hMeet] at hBase
  have hLeft : 0 ≤ G.predim (a ∩ x) :=
    hSparseA (a ∩ x) Finset.inter_subset_left
  change 0 ≤ G.predim x
  rw [hSplit]
  omega

/-- Symmetric formulation of preservation of 2-sparsity. -/
theorem twoSparse_union_of_noCross_right (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hSparseB : G.IsTwoSparse b)
    (hP : G.toPredimension.IsStrong (a ∩ b) a) :
    G.IsTwoSparse (a ∪ b) := by
  have hNoSwap : G.NoCrossEdges b a := by
    intro edge he
    have heAB : edge ∈ G.edgesWithin (a ∪ b) := by
      simpa only [Finset.union_comm] using he
    rcases Finset.mem_union.mp (hNo heAB) with heA | heB
    · exact Finset.mem_union.mpr (Or.inr heA)
    · exact Finset.mem_union.mpr (Or.inl heB)
  have hP' : G.toPredimension.IsStrong (b ∩ a) a := by
    simpa only [Finset.inter_comm] using hP
  simpa only [Finset.union_comm] using
    (G.twoSparse_union_of_noCross b a hNoSwap hSparseB hP')

end GraphOn
end BigHrushovski
