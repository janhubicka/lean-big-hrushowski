import BigHrushovski.FiniteCatalogue

/-!
# Finite realization of an applicable strong extension request

This module specializes the verified finite strong free-amalgamation
construction to the labelled diagrams used by the fair request catalogue.

If an abstract request A ≤ B is applicable to a finite strong stage C,
we can freely amalgamate C and B over A. The output has induced strong
copies of C and B, the prescribed base map commutes exactly, and there
are no accidental identifications.

This is the *finite response* step. Choosing these outputs coherently
along an infinite schedule and proving that the resulting chain covers
ℕ are separate obligations.
-/

namespace BigHrushovski
namespace FiniteCatalogue

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A labelled strong diagram applicable in a finite two-sparse graph
can be answered by a finite strong free amalgam. Both factor maps are
induced embeddings and identify only the prescribed common base.

Unlike `strongExtensionProperty_of_fairResponses`, no ambient infinite
graph or pre-existing response hypothesis is required. -/
theorem exists_finite_strong_response
    {n m : ℕ}
    (G : GraphOn V)
    (hSparse : G.IsTwoSparse (Finset.univ : Finset V))
    (diagram : StrongDiagram n m)
    (i : Fin n → V)
    (hi : Function.Injective i)
    (hInduced : ∀ x y : Fin n,
      diagram.source.adj x y ↔ G.adj (i x) (i y))
    (hStrong : G.toPredimension.IsStrong
      ((Finset.univ : Finset (Fin n)).image i)
      (Finset.univ : Finset V)) :
    ∃ (K : GraphOn (TaggedAmalgam.Carrier
          (Fin n) (FiniteSpan.Tail i)
          (FiniteSpan.Tail diagram.embedding)))
      (old : V → TaggedAmalgam.Carrier
          (Fin n) (FiniteSpan.Tail i)
          (FiniteSpan.Tail diagram.embedding))
      (answer : Fin m → TaggedAmalgam.Carrier
          (Fin n) (FiniteSpan.Tail i)
          (FiniteSpan.Tail diagram.embedding)),
      Function.Injective old ∧
      Function.Injective answer ∧
      (∀ x y : V, K.adj (old x) (old y) ↔ G.adj x y) ∧
      (∀ x y : Fin m,
        K.adj (answer x) (answer y) ↔ diagram.target.adj x y) ∧
      (∀ x : Fin n, old (i x) = answer (diagram.embedding x)) ∧
      (∀ (x : V) (y : Fin m), old x = answer y →
        ∃ p : Fin n, x = i p ∧ y = diagram.embedding p) ∧
      K.IsTwoSparse Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset V).image old) Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin m)).image answer) Finset.univ := by
  classical
  have hAgree : ∀ x y : Fin n,
      G.adj (i x) (i y) ↔
        diagram.target.adj (diagram.embedding x)
          (diagram.embedding y) := by
    intro x y
    exact (hInduced x y).symm.trans (diagram.induced x y)
  exact FiniteSpan.exists_finite_strong_free_amalgam
    G diagram.target i diagram.embedding hi diagram.inj
    hAgree hSparse diagram.sparseTarget hStrong diagram.strong

end FiniteCatalogue
end BigHrushovski
