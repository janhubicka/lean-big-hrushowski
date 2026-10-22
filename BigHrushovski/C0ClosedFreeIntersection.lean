import BigHrushovski.C0UnaryClosedStrong

/-!
# C0 unary-closed substructures meet freely

In the countable C0 minimal-component enumeration, the canonical
set-valued unary closure contains the whole component of a vertex
and every earlier endpoint of an edge leaving that component.

Consequently, two finite unary-closed vertex sets have no graph
edge between their exclusive parts. Together with the already
checked fact that unions are unary closed, this identifies their
actual induced union with the graph free amalgam over the
intersection.

This is a theorem about the concrete countable C0 generic,
not just the abstract assumptions of the companion big Ramsey
library. It does not assert the unverified functional Fraisse
limit identification or any TRAP theorem.
-/
namespace BigHrushovski
namespace FiniteCatalogue

/-- The closure system prevents a graph edge from crossing
between the two exclusive parts of closed substructures. -/
theorem genericC0UnaryClosed_noCrossExclusive
    (s t : Finset ℕ)
    (hs : IsGenericC0UnaryClosed s)
    (ht : IsGenericC0UnaryClosed t)
    {x y : ℕ}
    (hxs : x ∈ s) (hxt : x ∉ t)
    (hyt : y ∈ t) (hys : y ∉ s)
    (hxy : genericTwoSparseGraph.adj x y) : False := by
  by_cases heq :
      genericC0ComponentIndex x = genericC0ComponentIndex y
  · have hyComp :
        y ∈ genericC0Component (genericC0ComponentIndex x) :=
      (genericC0ComponentIndex_eq_iff y _).mp heq.symm
    have hyClosure : y ∈ genericC0UnaryClosure x :=
      genericC0UnaryClosure_contains_component x hyComp
    exact hys (hs x hxs hyClosure)
  · by_cases hlt :
        genericC0ComponentIndex x < genericC0ComponentIndex y
    · have hxOld :
          x ∈ genericC0MinimalStage (genericC0ComponentIndex y) :=
        (genericC0ComponentIndex_lt_iff_stage x _).mp hlt
      have hyComp :
          y ∈ genericC0Component (genericC0ComponentIndex y) :=
        genericC0ComponentIndex_mem y
      have hxT :
          x ∈ t :=
        genericC0UnaryClosed_backNeighbour t ht
          (genericC0ComponentIndex y) y x
          hyComp hyt hxOld (genericTwoSparseGraph.symm x y hxy)
      exact hxt hxT
    · have hgt :
          genericC0ComponentIndex y < genericC0ComponentIndex x := by omega
      have hyOld :
          y ∈ genericC0MinimalStage (genericC0ComponentIndex x) :=
        (genericC0ComponentIndex_lt_iff_stage y _).mp hgt
      have hxComp :
          x ∈ genericC0Component (genericC0ComponentIndex x) :=
        genericC0ComponentIndex_mem x
      have hyS :
          y ∈ s :=
        genericC0UnaryClosed_backNeighbour s hs
          (genericC0ComponentIndex x) x y
          hxComp hxs hyOld hxy
      exact hys hyS

/-- Every edge in the union of two unary-closed sets
is contained entirely in one of the two sets.
The induced union is therefore the free graph amalgam. -/
theorem genericC0UnaryClosed_unionEdges
    (s t : Finset ℕ)
    (hs : IsGenericC0UnaryClosed s)
    (ht : IsGenericC0UnaryClosed t)
    {x y : ℕ}
    (hx : x ∈ s ∪ t) (hy : y ∈ s ∪ t)
    (hxy : genericTwoSparseGraph.adj x y) :
    (x ∈ s ∧ y ∈ s) ∨ (x ∈ t ∧ y ∈ t) := by
  rcases Finset.mem_union.mp hx with hxs | hxt
  · rcases Finset.mem_union.mp hy with hys | hyt
    · exact Or.inl ⟨hxs, hys⟩
    · by_cases hxt : x ∈ t
      · exact Or.inr ⟨hxt, hyt⟩
      · by_cases hys : y ∈ s
        · exact Or.inl ⟨hxs,hys⟩
        · exact False.elim
            (genericC0UnaryClosed_noCrossExclusive s t hs ht
              hxs hxt hyt hys hxy)
  · rcases Finset.mem_union.mp hy with hys | hyt
    · by_cases hxs : x ∈ s
      · exact Or.inl ⟨hxs,hys⟩
      · by_cases hyt : y ∈ t
        · exact Or.inr ⟨hxt,hyt⟩
        · exact False.elim
            (genericC0UnaryClosed_noCrossExclusive s t hs ht
              hys hyt hxt hxs
              (genericTwoSparseGraph.symm x y hxy))
    · exact Or.inr ⟨hxt,hyt⟩

/-- Closed sets are stable under union, so no further vertices
are introduced by closing a finite union of complete components. -/
theorem genericC0UnaryClosed_unionIsClosed
    (s t : Finset ℕ)
    (hs : IsGenericC0UnaryClosed s)
    (ht : IsGenericC0UnaryClosed t) :
    IsGenericC0UnaryClosed (s ∪ t) :=
  genericC0UnaryClosed_union hs ht

end FiniteCatalogue
end BigHrushovski
