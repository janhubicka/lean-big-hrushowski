import BigHrushovski.FreeAmalgam
import BigHrushovski.GlobalClosure

/-!
# Strength of a union closed under old-neighbour dependencies

Suppose x is strong in an old finite set a, and B is a new block,
disjoint from a, with no edge connecting B to a \ x.
Then x union B is strong in a union B.

This is the finite predimension step used in the C0 unary-closure
presentation. The no-cross hypothesis makes explicit the closure
under back edges; simply being a union of whole blocks is not
sufficient. The lemma does not construct the unary closure
function or its associated Fraisse class.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- Adding an entire new block to an old strong subset remains
strong, provided no edge joins that block to an omitted old
vertex. -/
theorem closedBlock_strong_of_noCross
    (a x B : Finset V)
    (hx : G.toPredimension.IsStrong x a)
    (hDisj : Disjoint a B)
    (hNo : G.NoCrossEdges a (x ∪ B)) :
    G.toPredimension.IsStrong (x ∪ B) (a ∪ B) := by
  have hCap : a ∩ (x ∪ B) = x := by
    ext v
    constructor
    · intro hv
      obtain ⟨hva, hxb⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hxb with hvx | hvB
      · exact hvx
      · exact ((Finset.disjoint_left.mp hDisj) hva hvB).elim
    · intro hv
      exact Finset.mem_inter.mpr
        ⟨hx.1 hv, Finset.mem_union.mpr (Or.inl hv)⟩
  have hStrong :
      G.toPredimension.IsStrong (x ∪ B) (a ∪ (x ∪ B)) :=
    G.strong_right_of_noCross a (x ∪ B) hNo
      (by simpa only [hCap] using hx)
  have hUnion : a ∪ (x ∪ B) = a ∪ B := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvXB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · rcases Finset.mem_union.mp hvXB with hvX | hvB
        · exact Finset.mem_union.mpr (Or.inl (hx.1 hvX))
        · exact Finset.mem_union.mpr (Or.inr hvB)
    · intro hv
      rcases Finset.mem_union.mp hv with hvA | hvB
      · exact Finset.mem_union.mpr (Or.inl hvA)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inr hvB)))
  rw [hUnion] at hStrong
  exact hStrong

/-- The same union is globally strong when the complete new prefix
is globally strong in the ambient graph. -/
theorem closedBlock_global_of_noCross
    (a x B : Finset V)
    (hx : G.toPredimension.IsStrong x a)
    (hDisj : Disjoint a B)
    (hNo : G.NoCrossEdges a (x ∪ B))
    (hGlobal : G.toPredimension.IsGloballyStrong (a ∪ B)) :
    G.toPredimension.IsGloballyStrong (x ∪ B) :=
  G.toPredimension.globallyStrong_of_strong_in_global
    (G.closedBlock_strong_of_noCross a x B hx hDisj hNo) hGlobal

end GraphOn
end BigHrushovski
