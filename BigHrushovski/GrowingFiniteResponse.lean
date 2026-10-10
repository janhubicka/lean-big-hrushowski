import BigHrushovski.FiniteResponse
import BigHrushovski.ForcedGrowth
import BigHrushovski.StrongEmbeddingComposition

/-!
# Answering a finite strong extension request with strict growth

A response from finite strong free amalgamation may add no vertices
when its target is already present. An infinite fair construction cannot
simply stop on such stages: to exhaust the Nat carrier, each successor
must add a genuinely fresh vertex.

First realize the labelled strong diagram over an applicable strong
source in the old stage. Then freely adjoin an isolated vertex over the
empty strong base. Composition of strong induced embeddings ensures
that both the old stage and the answered diagram remain strong after
this second extension. The new isolated point is outside the old image.

This is an existential *finite* successor theorem, not the construction
of a coherent infinite sequence or the generic countable graph.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- The finite free-amalgam carrier of an applicable labelled request. -/
abbrev ResponseCarrier {n m : ℕ} {V : Type*}
    (i : Fin n → V) (diagram : StrongDiagram n m) :=
  TaggedAmalgam.Carrier (Fin n)
    (FiniteSpan.Tail i) (FiniteSpan.Tail diagram.embedding)

/-- The carrier after forcing one additional vertex. -/
abbrev GrowingResponseCarrier {n m : ℕ} {V : Type*}
    (i : Fin n → V) (diagram : StrongDiagram n m) :=
  FiniteSpan.JointCarrier (ResponseCarrier i diagram) Unit

/-- Every applicable finite strong request can be realized while
strictly increasing the finite domain. The old stage and the target
of the request are both induced strong subgraphs of the output. -/
theorem exists_growing_finite_strong_response
    {V : Type*} [Fintype V] [DecidableEq V]
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
    ∃ (K : GraphOn (GrowingResponseCarrier i diagram))
      (old : V → GrowingResponseCarrier i diagram)
      (answer : Fin m → GrowingResponseCarrier i diagram)
      (fresh : GrowingResponseCarrier i diagram),
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
        ((Finset.univ : Finset (Fin m)).image answer) Finset.univ ∧
      fresh ∉ (Finset.univ : Finset V).image old := by
  classical
  obtain ⟨H, f, g, hf, hg, hIndF, hIndG, hBase, hOnlyBase,
      hSparseH, hStrongF, hStrongG⟩ :=
    exists_finite_strong_response G hSparse diagram i
      hi hInduced hStrong
  obtain ⟨K, k, fresh, hk, hIndK, hSparseK, hStrongK, hFresh⟩ :=
    FiniteSpan.exists_fresh_strong_extension H hSparseH
  let old : V → GrowingResponseCarrier i diagram := k ∘ f
  let answer : Fin m → GrowingResponseCarrier i diagram := k ∘ g
  have hStrongOld :
      K.toPredimension.IsStrong
        ((Finset.univ : Finset V).image old) Finset.univ := by
    exact H.strong_image_trans_of_induced K f k hk
      (fun x y => (hIndK x y).symm) hStrongF hStrongK
  have hStrongAnswer :
      K.toPredimension.IsStrong
        ((Finset.univ : Finset (Fin m)).image answer) Finset.univ := by
    exact H.strong_image_trans_of_induced K g k hk
      (fun x y => (hIndK x y).symm) hStrongG hStrongK
  refine ⟨K, old, answer, fresh, hk.comp hf, hk.comp hg,
    ?_, ?_, ?_, ?_, hSparseK, hStrongOld, hStrongAnswer, ?_⟩
  · intro x y
    exact (hIndK (f x) (f y)).trans (hIndF x y)
  · intro x y
    exact (hIndK (g x) (g y)).trans (hIndG x y)
  · intro x
    exact congrArg k (hBase x)
  · intro x y h
    exact hOnlyBase x y (hk h)
  · intro hMem
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hMem
    apply hFresh
    exact Finset.mem_image.mpr
      ⟨f v, Finset.mem_univ _, hv⟩

end FiniteCatalogue
end BigHrushovski
