import BigHrushovski.C0CoordinateNormalForm

/-!
# Literal finite-coordinate code for one-generated C₀ diagrams

A finite ordered one-generated closure may be represented without an
isomorphism quotient: retain its finite natural-number support, its
pointed coordinate, and the complete edge and closure-incidence matrices.

This file checks that these matrices preserve and reflect *all* edge and
unary-value incidences. In particular a code cannot forget nonedges, or
identify two distinct complete set-valued closures.

The predicates selecting the permitted finite C₀ diagrams, their closed
subcode operation, and the global coordinate host W remain separate.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]

/-- Complete ordered-pair incidence of a finite graph, including both
orientations of each undirected edge. Its absence records nonedges. -/
noncomputable def coordinateAdjacencyPairs
    (G : GraphOn U) (e : U ↪o ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p : U × U => G.adj p.1 p.2)).image
      (fun p => (e p.1, e p.2))

/-- The complete vertex-valued unary function as an incidence matrix.
This records every member of every C-value, not only its cardinality. -/
noncomputable def coordinateClosurePairs
    (C : U → Finset U) (e : U ↪o ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p : U × U => p.2 ∈ C p.1)).image
      (fun p => (e p.1, e p.2))

/-- Every entry of the coded adjacency matrix recovers and reflects
exactly the original adjacency relation. -/
theorem mem_coordinateAdjacencyPairs_iff
    (G : GraphOn U) (e : U ↪o ℕ) (u v : U) :
    (e u, e v) ∈ coordinateAdjacencyPairs G e ↔
      G.adj u v := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    rcases p with ⟨x, y⟩
    have hx : x = u := e.injective (congrArg Prod.fst heq)
    have hy : y = v := e.injective (congrArg Prod.snd heq)
    have hAdj : G.adj x y := (Finset.mem_filter.mp hp).2
    simpa only [hx, hy] using hAdj
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(u, v), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩

/-- Every entry of the coded unary matrix recovers and reflects
membership in the complete original unary value. -/
theorem mem_coordinateClosurePairs_iff
    (C : U → Finset U) (e : U ↪o ℕ) (u v : U) :
    (e u, e v) ∈ coordinateClosurePairs C e ↔
      v ∈ C u := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    rcases p with ⟨x, y⟩
    have hx : x = u := e.injective (congrArg Prod.fst heq)
    have hy : y = v := e.injective (congrArg Prod.snd heq)
    have hC : y ∈ C x := (Finset.mem_filter.mp hp).2
    simpa only [hx, hy] using hC
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(u, v), ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩

/-- The data of a pointed finite diagram after increasing labelling.
No abstract finite type or arbitrary representative remains. -/
structure LiteralPointedCode where
  support : Finset ℕ
  point : ℕ
  point_mem : point ∈ support
  adjacencyPairs : Finset (ℕ × ℕ)
  closurePairs : Finset (ℕ × ℕ)

/-- Canonical finite pointed code of a source graph and complete unary
values under a chosen increasing natural-coordinate assignment. -/
noncomputable def literalPointedCode
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (u : U) : LiteralPointedCode where
  support := labelSupport e
  point := e u
  point_mem := Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩
  adjacencyPairs := coordinateAdjacencyPairs G e
  closurePairs := coordinateClosurePairs C e

@[simp] theorem literalPointedCode_point
    (G : GraphOn U) (C : U → Finset U)
    (e : U ↪o ℕ) (u : U) :
    (literalPointedCode G C e u).point = e u := rfl

/-- An equality of canonical codes forces equality of ALL edge and
nonedge facts, not merely an inclusion of adjacency relations. -/
theorem literalPointedCode_eq_reflects_adj
    (G H : GraphOn U) (C D : U → Finset U)
    (e : U ↪o ℕ) (root : U)
    (heq : literalPointedCode G C e root =
      literalPointedCode H D e root)
    (u v : U) : G.adj u v ↔ H.adj u v := by
  have hPairs : coordinateAdjacencyPairs G e =
      coordinateAdjacencyPairs H e :=
    congrArg LiteralPointedCode.adjacencyPairs heq
  rw [← mem_coordinateAdjacencyPairs_iff G e u v,
      hPairs, mem_coordinateAdjacencyPairs_iff H e u v]

/-- The same equality also forces equality of all individual members
of all complete unary values. -/
theorem literalPointedCode_eq_reflects_closure
    (G H : GraphOn U) (C D : U → Finset U)
    (e : U ↪o ℕ) (root : U)
    (heq : literalPointedCode G C e root =
      literalPointedCode H D e root)
    (u v : U) : v ∈ C u ↔ v ∈ D u := by
  have hPairs : coordinateClosurePairs C e =
      coordinateClosurePairs D e :=
    congrArg LiteralPointedCode.closurePairs heq
  rw [← mem_coordinateClosurePairs_iff C e u v,
      hPairs, mem_coordinateClosurePairs_iff D e u v]

end FiniteUnaryCoordinates
end BigHrushovski
