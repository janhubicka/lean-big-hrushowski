import BigHrushovski.StrongForth

/-!
# Extending finite strong partial isomorphisms in the reverse direction

The back extension lemma is the forth extension theorem applied to
the inverse partial equivalence, with the two graphs interchanged.
It extends the range of a finite strong partial isomorphism to contain
any prescribed target vertex, while preserving induced adjacency,
all original values, and global self-sufficiency of both finite domains.

Neither lemma by itself constructs the alternating countable union;
that is the remaining back-and-forth argument.
-/

namespace BigHrushovski
namespace FiniteCatalogue

/-- Every prescribed target vertex can be incorporated in a finite
globally strong range of an induced strong partial isomorphism. -/
theorem exists_strong_back
    (M N : GraphOn ℕ)
    (hSparseN : ∀ s : Finset ℕ, 0 ≤ N.predim s)
    (hCoverN : Predimension.FiniteStrongCover N.toPredimension)
    (hExtM : HasStrongExtensionProperty M)
    (a b : Finset ℕ)
    (ha : M.toPredimension.IsGloballyStrong a)
    (hb : N.toPredimension.IsGloballyStrong b)
    (p : {x : ℕ // x ∈ a} ≃ {x : ℕ // x ∈ b})
    (hIndP : ∀ x y : {x : ℕ // x ∈ a},
      M.adj x.val y.val ↔ N.adj (p x).val (p y).val)
    (v : ℕ) :
    ∃ (d : Finset ℕ) (hbd : b ⊆ d),
      v ∈ d ∧
      N.toPredimension.IsGloballyStrong d ∧
      ∃ h : {x : ℕ // x ∈ d} → ℕ,
        Function.Injective h ∧
        (∀ x y : {x : ℕ // x ∈ d},
          N.adj x.val y.val ↔ M.adj (h x) (h y)) ∧
        (∀ x : {x : ℕ // x ∈ b},
          h ⟨x.val, hbd x.property⟩ = (p.symm x).val) ∧
        M.toPredimension.IsGloballyStrong
          ((Finset.univ : Finset {x : ℕ // x ∈ d}).image h) := by
  have hIndInverse : ∀ x y : {x : ℕ // x ∈ b},
      N.adj x.val y.val ↔
        M.adj (p.symm x).val (p.symm y).val := by
    intro x y
    simpa using (hIndP (p.symm x) (p.symm y)).symm
  exact exists_strong_forth N M hSparseN hCoverN hExtM
    b a hb ha p.symm hIndInverse v

end FiniteCatalogue
end BigHrushovski
