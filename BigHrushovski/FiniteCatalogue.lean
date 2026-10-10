import BigHrushovski.C0StrongAge
import Mathlib.Logic.Encodable.Basic

/-!
# Countable catalogues of finite strong extension diagrams

Every finite graph has a labelled presentation on some Fin n. For
fixed n there are only finitely many graph relations on Fin n. The
same holds for strong induced-embedding diagrams with source Fin n
and target Fin m. Thus both finite graph presentations and finite
strong-extension requirements admit countable encodings.

This is the enumeration input for the strong Fraïssé construction.
It does not yet schedule requirements against a growing generic graph.
-/

namespace BigHrushovski

namespace FiniteCatalogue

/-- A finite carrier supports only finitely many undirected graph
relations, including all symmetric irreflexive possibilities. -/
noncomputable instance finite_graphOn_fin (n : ℕ) :
    Finite (GraphOn (Fin n)) := by
  classical
  have h : Function.Injective
      (fun G : GraphOn (Fin n) => G.adj) := by
    intro G H hEq
    cases G
    cases H
    cases hEq
    rfl
  exact Finite.of_injective (fun G : GraphOn (Fin n) => G.adj) h

/-- Labelled finite 2-sparse graphs, with vertex set Fin n for some n. -/
abbrev LabelledC0 :=
  Σ n : ℕ, { G : GraphOn (Fin n) //
      G.IsTwoSparse (Finset.univ : Finset (Fin n)) }

noncomputable instance : Countable LabelledC0 := by
  infer_instance

/-- A labelled strong extension requirement: a finite 2-sparse graph
A, a finite 2-sparse graph B, and an induced strong embedding A → B.
Both graphs are carried by finite ordinal vertex sets. -/
structure StrongDiagram (n m : ℕ) where
  source : GraphOn (Fin n)
  target : GraphOn (Fin m)
  embedding : Fin n → Fin m
  inj : Function.Injective embedding
  induced : ∀ x y : Fin n,
    source.adj x y ↔ target.adj (embedding x) (embedding y)
  sparseSource : source.IsTwoSparse (Finset.univ : Finset (Fin n))
  sparseTarget : target.IsTwoSparse (Finset.univ : Finset (Fin m))
  strong : target.toPredimension.IsStrong
    ((Finset.univ : Finset (Fin n)).image embedding)
    (Finset.univ : Finset (Fin m))

/-- Only finitely many strong diagrams occur at a fixed pair of sizes. -/
noncomputable instance finite_strongDiagram (n m : ℕ) :
    Finite (StrongDiagram n m) := by
  classical
  have h : Function.Injective
      (fun d : StrongDiagram n m => (d.source, d.target, d.embedding)) := by
    intro d e hEq
    cases d
    cases e
    cases hEq
    rfl
  exact Finite.of_injective
    (fun d : StrongDiagram n m => (d.source, d.target, d.embedding)) h

/-- All labelled finite strong extension requests. -/
abbrev StrongDiagramCatalogue :=
  Σ n : ℕ, Σ m : ℕ, StrongDiagram n m

noncomputable instance : Countable StrongDiagramCatalogue := by
  infer_instance

/-- Choose a countable encoding of every finite strong diagram. -/
noncomputable instance : Encodable StrongDiagramCatalogue :=
  Encodable.ofCountable StrongDiagramCatalogue

/-- A possibly sparse enumeration of all finite strong diagrams. -/
noncomputable def decodeStrongDiagram (code : ℕ) :
    Option StrongDiagramCatalogue :=
  (Encodable.decode : ℕ → Option StrongDiagramCatalogue) code

/-- Every finite strong diagram has a code. -/
theorem decodeStrongDiagram_encode (d : StrongDiagramCatalogue) :
    decodeStrongDiagram (Encodable.encode d) = some d := by
  exact Encodable.encodek d

theorem strongDiagram_occurs (d : StrongDiagramCatalogue) :
    ∃ k : ℕ, decodeStrongDiagram k = some d :=
  ⟨Encodable.encode d, decodeStrongDiagram_encode d⟩

end FiniteCatalogue
end BigHrushovski
