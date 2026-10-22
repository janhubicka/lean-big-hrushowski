import BigHrushovski.CFLocalSupportTransport

/-!
# Old-neighbour sets under embeddings of finite induced subgraphs

A map defined (or known to be induced) only on a finite ambient
vertex set C transports the complete neighbour set of B among A,
whenever A,B ⊆ C. No inducedness or injectivity outside C is
needed; in fact injectivity is unnecessary for the neighbour-set
equality itself.

This is reusable in both C_0 and C_F support recovery, where the
map is an embedding of a finite closed substructure rather than
a globally induced self-map of the countable generic.
-/

namespace BigHrushovski
namespace GraphOn

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Exact transport of all old neighbours of a finite set B
among a finite set A, under adjacency iff **only on the finite
ambient C**. No graph information outside C is assumed. -/
theorem oldNeighbourSet_image_on
    (G : GraphOn U) (H : GraphOn V)
    (f : U → V) (C : Finset U)
    (hAdj : ∀ u ∈ C, ∀ v ∈ C,
      G.adj u v ↔ H.adj (f u) (f v))
    (A B : Finset U)
    (hA : A ⊆ C) (hB : B ⊆ C) :
    (G.oldNeighbourSet A B).image f =
      H.oldNeighbourSet (A.image f) (B.image f) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨v, hvN, hfv⟩ := Finset.mem_image.mp hy
    change v ∈ A.filter
      (fun w => ∃ u : U, u ∈ B ∧ G.adj u w) at hvN
    obtain ⟨hvA, u, huB, hEdge⟩ := Finset.mem_filter.mp hvN
    change y ∈ (A.image f).filter
      (fun w => ∃ u : V, u ∈ B.image f ∧ H.adj u w)
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨v, hvA, hfv⟩
    · refine ⟨f u, Finset.mem_image.mpr ⟨u, huB, rfl⟩, ?_⟩
      rw [← hfv]
      exact (hAdj u (hB huB) v (hA hvA)).mp hEdge
  · intro hy
    change y ∈ (A.image f).filter
      (fun w => ∃ u : V, u ∈ B.image f ∧ H.adj u w) at hy
    obtain ⟨hyA, w, hwB, hEdge⟩ := Finset.mem_filter.mp hy
    obtain ⟨v, hvA, hfv⟩ := Finset.mem_image.mp hyA
    obtain ⟨u, huB, hfu⟩ := Finset.mem_image.mp hwB
    have hSourceEdge : G.adj u v := by
      apply (hAdj u (hB huB) v (hA hvA)).mpr
      simpa only [hfu, hfv] using hEdge
    refine Finset.mem_image.mpr ⟨v, ?_, hfv⟩
    change v ∈ A.filter
      (fun z => ∃ q : U, q ∈ B ∧ G.adj q z)
    exact Finset.mem_filter.mpr ⟨hvA, ⟨u, huB, hSourceEdge⟩⟩

end GraphOn
end BigHrushovski
