import BigHrushovski.InfiniteGraph

/-!
# Predimension across a free graph amalgam

If no edge joining two finite vertex sets is missing from both induced
pieces, the edge count is modular across their union. Consequently a
strong common base remains strong after adjoining the other piece.

The vertex sets may lie in an infinite graph. This is a lemma about the
induced finite configuration; constructing arbitrary amalgams and proving
the age of 2-sparse graphs has free amalgamation remain separate tasks.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Every edge in the union is already an edge of at least one factor.
This is precisely the absence of edges across the two disjoint tails. -/
def NoCrossEdges (a b : Finset V) : Prop :=
  G.edgesWithin (a ∪ b) ⊆
    G.edgesWithin a ∪ G.edgesWithin b

/-- The edges of a no-crossing union are the union of the factor edges. -/
theorem edgesWithin_union_eq (a b : Finset V)
    (hNo : G.NoCrossEdges a b) :
    G.edgesWithin (a ∪ b) =
      G.edgesWithin a ∪ G.edgesWithin b :=
  le_antisymm hNo (G.edgesWithin_union_subset a b)

/-- The graph predimension is modular across a no-crossing union. -/
theorem predim_modular_of_noCross (a b : Finset V)
    (hNo : G.NoCrossEdges a b) :
    G.predim (a ∪ b) + G.predim (a ∩ b) =
      G.predim a + G.predim b := by
  have hVertex := Finset.card_union_add_card_inter a b
  have hEdge :=
    Finset.card_union_add_card_inter (G.edgesWithin a) (G.edgesWithin b)
  have hUnion := G.edgesWithin_union_eq a b hNo
  have hInter := G.edgesWithin_inter a b
  unfold predim
  rw [hUnion, hInter]
  omega

/-- No-crossing remains true if the second factor is shrunk to a set
containing the original overlap. -/
theorem noCross_restrict_right (a b c : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hcb : c ⊆ b) (hbase : a ∩ b ⊆ c) :
    G.NoCrossEdges a c := by
  intro edge he
  have hACb : a ∪ c ⊆ a ∪ b :=
    Finset.union_subset Finset.subset_union_left
      (hcb.trans Finset.subset_union_right)
  have heUnion : edge ∈ G.edgesWithin (a ∪ b) := by
    rcases (G.mem_edgesWithin_iff (a ∪ c) edge).mp he with
      ⟨hSub, hEdge⟩
    exact (G.mem_edgesWithin_iff (a ∪ b) edge).mpr
      ⟨hSub.trans hACb, hEdge⟩
  rcases Finset.mem_union.mp (hNo heUnion) with heA | heB
  · exact Finset.mem_union.mpr (Or.inl heA)
  · have hSubB := ((G.mem_edgesWithin_iff b edge).mp heB).1
    have hSubAC := ((G.mem_edgesWithin_iff (a ∪ c) edge).mp he).1
    have hSubC : edge ⊆ c := by
      intro v hv
      rcases Finset.mem_union.mp (hSubAC hv) with hvA | hvC
      · exact hbase (Finset.mem_inter.mpr ⟨hvA, hSubB hv⟩)
      · exact hvC
    exact Finset.mem_union.mpr (Or.inr
      ((G.mem_edgesWithin_iff c edge).mpr
        ⟨hSubC, ((G.mem_edgesWithin_iff b edge).mp heB).2⟩))

/-- In a free join, the left factor is strong whenever the overlap is
strong in the right factor. -/
theorem strong_left_of_noCross (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hP : G.toPredimension.IsStrong (a ∩ b) b) :
    G.toPredimension.IsStrong a (a ∪ b) := by
  refine ⟨Finset.subset_union_left, ?_⟩
  intro x hax hxab
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
  have hmod := G.predim_modular_of_noCross a c hNoC
  rw [hPcap] at hmod
  have hbase : G.predim (a ∩ b) ≤ G.predim c := hP.2 c hPsub hcb
  change G.predim a ≤ G.predim x
  rw [hXeq]
  omega

/-- The symmetric strong-preservation statement for the right factor. -/
theorem strong_right_of_noCross (a b : Finset V)
    (hNo : G.NoCrossEdges a b)
    (hP : G.toPredimension.IsStrong (a ∩ b) a) :
    G.toPredimension.IsStrong b (a ∪ b) := by
  have hSwap : G.NoCrossEdges b a := by
    intro edge he
    have heAB : edge ∈ G.edgesWithin (a ∪ b) := by
      simpa only [Finset.union_comm] using he
    rcases Finset.mem_union.mp (hNo heAB) with heA | heB
    · exact Finset.mem_union.mpr (Or.inr heA)
    · exact Finset.mem_union.mpr (Or.inl heB)
  have hP' : G.toPredimension.IsStrong (b ∩ a) a := by
    simpa only [Finset.inter_comm] using hP
  simpa only [Finset.union_comm] using
    (G.strong_left_of_noCross b a hSwap hP')

end GraphOn
end BigHrushovski
