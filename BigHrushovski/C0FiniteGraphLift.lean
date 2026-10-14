import BigHrushovski.C0FiniteStrongFactorization
import BigHrushovski.SpanNormalization

/-!
# Finite graph-extension lifting over an arbitrary embedded strong base

Suppose A ≤ C and A ≤ B are finite induced strong graph embeddings,
not necessarily inclusions and with no unary closure assumed on A.
Normalize the two embeddings to tagged disjoint tails, form the
verified strong free graph amalgam D = C ⊕_A B, and then decompose
the strong inclusion C ≤ D into minimal strong steps using the
absolute finite factorisation lemma.

The endpoint supplies graph data for the manuscript's reduct
argument. The remaining functional obligation is to equip the newly
added minimal blocks with their complete unary dependency closures
without changing the already named function on C.
-/

namespace BigHrushovski
namespace FiniteSpan

/-- The finite graph strong-extension lifting lemma, allowing the
common strong base to be an arbitrary embedded finite graph rather
than a closed functional substructure. Both factor embeddings are
induced and strong, and the old factor has a finite minimal strong
decomposition into the amalgam. -/
theorem exists_strong_amalgam_with_minimal_steps
    {P C B : Type*}
    [Fintype P] [Fintype C] [Fintype B]
    [DecidableEq P] [DecidableEq C] [DecidableEq B]
    (G : GraphOn C) (H : GraphOn B)
    (i : P → C) (j : P → B)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q))
    (hSparseG : G.IsTwoSparse (Finset.univ : Finset C))
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset B))
    (hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i) Finset.univ)
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset P).image j) Finset.univ) :
    ∃ (K : GraphOn (TaggedAmalgam.Carrier P (Tail i) (Tail j)))
      (f : C → TaggedAmalgam.Carrier P (Tail i) (Tail j))
      (g : B → TaggedAmalgam.Carrier P (Tail i) (Tail j)),
      Function.Injective f ∧ Function.Injective g ∧
      (∀ x y : C, K.adj (f x) (f y) ↔ G.adj x y) ∧
      (∀ x y : B, K.adj (g x) (g y) ↔ H.adj x y) ∧
      (∀ p : P, f (i p) = g (j p)) ∧
      (∀ x : C, ∀ y : B, f x = g y →
        ∃ p : P, x = i p ∧ y = j p) ∧
      K.IsTwoSparse (Finset.univ :
        Finset (TaggedAmalgam.Carrier P (Tail i) (Tail j))) ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset C).image f) Finset.univ ∧
      K.toPredimension.IsStrong
        ((Finset.univ : Finset B).image g) Finset.univ ∧
      Predimension.MinimalStrongChain K.toPredimension
        ((Finset.univ : Finset C).image f) Finset.univ := by
  classical
  obtain ⟨K, f, g, hf, hg, hAdjF, hAdjG, hBase, hOnly,
      hSparse, hStrongF, hStrongG'⟩ :=
    exists_finite_strong_free_amalgam
      G H i j hi hj hAgree hSparseG hSparseH hStrongG hStrongH
  exact ⟨K, f, g, hf, hg, hAdjF, hAdjG, hBase, hOnly,
    hSparse, hStrongF, hStrongG',
    K.toPredimension.finite_minimal_decomposition_of_strong_absolute hStrongF⟩

end FiniteSpan
end BigHrushovski
