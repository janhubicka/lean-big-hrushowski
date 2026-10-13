import BigHrushovski.C0ClosedUnions

/-!
# Back-neighbour criterion for a no-crossing block union

Suppose x is an old selected subset of a, and B is a block
of new vertices. If every neighbour in a of every vertex
of B belongs to x, then the graph union a ∪ (x ∪ B)
has no edge across the two disjoint tails.

The proof works with unordered two-element graph edges.
An edge crossing from B into a \ x would contradict the
back-neighbour assumption. This is the missing combinatorial
interface between unary closure under back edges and the
already certified no-cross strongness lemma.
-/

namespace BigHrushovski
namespace GraphOn

variable {V : Type*} [DecidableEq V] (G : GraphOn V)

/-- An unordered graph edge connects every two distinct members.
The two-element condition is essential. -/
theorem adj_of_IsEdge_of_distinct
    (e : Finset V) (he : G.IsEdge e)
    {u v : V} (hu : u ∈ e) (hv : v ∈ e)
    (huv : u ≠ v) : G.adj u v := by
  classical
  rcases he with ⟨hcard, p, hp, q, hq, hpq⟩
  have hpqNe : p ≠ q := by
    intro heq
    subst q
    exact (G.irrefl p) hpq
  have hPairSub : (insert p ({q} : Finset V)) ⊆ e := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzp | hzq
    · subst z
      exact hp
    · have hzEq : z = q := Finset.mem_singleton.mp hzq
      subst z
      exact hq
  have hPairCard : (insert p ({q} : Finset V)).card = 2 := by
    simp [hpqNe]
  have hEq : e = insert p ({q} : Finset V) := by
    have hh : (insert p ({q} : Finset V)) = e :=
      Finset.eq_of_subset_of_card_le hPairSub (by omega)
    exact hh.symm
  have huPair : u = p ∨ u = q := by
    have hu' : u ∈ insert p ({q} : Finset V) := by
      rw [← hEq]
      exact hu
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hu'
  have hvPair : v = p ∨ v = q := by
    have hv' : v ∈ insert p ({q} : Finset V) := by
      rw [← hEq]
      exact hv
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hv'
  rcases huPair with hup | huq
  · rcases hvPair with hvp | hvq
    · exact (huv (hup.trans hvp.symm)).elim
    · simpa only [hup, hvq] using hpq
  · rcases hvPair with hvp | hvq
    · simpa only [huq, hvp] using G.symm p q hpq
    · exact (huv (huq.trans hvq.symm)).elim

/-- No crossing edges when a new block has no old neighbour
outside a prescribed selected subset x of the old prefix a.
There is no assumption here that the selected set is strong. -/
theorem noCross_of_backNeighbours
    (a x B : Finset V)
    (hx : x ⊆ a)
    (hBack : ∀ u ∈ B, ∀ v ∈ a, G.adj u v → v ∈ x) :
    G.NoCrossEdges a (x ∪ B) := by
  classical
  intro e he
  obtain ⟨heSub, heEdge⟩ :=
    (G.mem_edgesWithin_iff (a ∪ (x ∪ B)) e).mp he
  by_cases heA : e ⊆ a
  · exact Finset.mem_union.mpr (Or.inl
      ((G.mem_edgesWithin_iff a e).mpr ⟨heA, heEdge⟩))
  by_cases heXB : e ⊆ x ∪ B
  · exact Finset.mem_union.mpr (Or.inr
      ((G.mem_edgesWithin_iff (x ∪ B) e).mpr ⟨heXB, heEdge⟩))
  exfalso
  have hexu : ∃ u : V, u ∈ e ∧ u ∉ a := by
    by_contra hnone
    apply heA
    intro u hu
    by_contra hna
    exact hnone ⟨u, hu, hna⟩
  obtain ⟨u, huE, huA⟩ := hexu
  have huB : u ∈ B := by
    rcases Finset.mem_union.mp (heSub huE) with hOld | hNew
    · exact (huA hOld).elim
    · rcases Finset.mem_union.mp hNew with huX | huB
      · exact (huA (hx huX)).elim
      · exact huB
  have hexv : ∃ v : V, v ∈ e ∧ v ∉ x ∪ B := by
    by_contra hnone
    apply heXB
    intro v hv
    by_contra hnXB
    exact hnone ⟨v, hv, hnXB⟩
  obtain ⟨v, hvE, hvXB⟩ := hexv
  have hvA : v ∈ a := by
    rcases Finset.mem_union.mp (heSub hvE) with hOld | hNew
    · exact hOld
    · exact (hvXB hNew).elim
  have huv : u ≠ v := by
    intro heq
    subst v
    exact huA hvA
  have hAdj : G.adj u v :=
    G.adj_of_IsEdge_of_distinct e heEdge huE hvE huv
  have hvX : v ∈ x := hBack u huB v hvA hAdj
  exact hvXB (Finset.mem_union.mpr (Or.inl hvX))

end GraphOn
end BigHrushovski
