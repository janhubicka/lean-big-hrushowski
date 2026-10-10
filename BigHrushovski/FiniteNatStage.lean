import BigHrushovski.SpanNormalization

/-!
# Finite stage graphs on consecutive natural-number intervals

To answer a fair request `Fin n → ℕ` inside the current finite stage,
one needs the finite graph on `Fin m` induced by the stage graph on ℕ.
The canonical injection `Fin m → ℕ` has image exactly `range m`.
The predimension and finite strongness conditions are invariant under
this induced representation.

These statements bridge the Nat-indexed request schedule with the
finite-carrier free-amalgamation theorems. They do not construct a
recursive fair responding sequence.
-/

namespace BigHrushovski
namespace GraphOn

/-- The numeric labels of Fin m form exactly the first m naturals. -/
theorem image_fin_val_univ (m : ℕ) :
    (Finset.univ : Finset (Fin m)).image
      (fun i : Fin m => i.val) = Finset.range m := by
  classical
  ext k
  simp only [Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact i.isLt
  · intro hk
    exact ⟨⟨k, hk⟩, rfl⟩

/-- Two-sparsity on a consecutive finite Nat stage is equivalent to
two-sparsity of the graph pulled back to Fin m. -/
theorem twoSparse_pullback_fin_iff
    (G : GraphOn ℕ) (m : ℕ) :
    (G.pullback (fun i : Fin m => i.val)).IsTwoSparse Finset.univ ↔
      G.IsTwoSparse (Finset.range m) := by
  classical
  have hAdj : ∀ i j : Fin m,
      (G.pullback (fun x : Fin m => x.val)).adj i j ↔
        G.adj i.val j.val := by
    intro i j
    rfl
  have h :=
    (G.pullback (fun i : Fin m => i.val)).twoSparse_image_iff G
      (fun i : Fin m => i.val)
      (by
        intro i j hij
        exact Fin.ext hij)
      hAdj (Finset.univ : Finset (Fin m))
  rw [image_fin_val_univ m] at h
  exact h.symm

/-- A strong substructure of the finite induced Nat stage is
equivalent to its pulled-back strong substructure on Fin m. -/
theorem strong_pullback_fin_iff
    (G : GraphOn ℕ) (m : ℕ) (a : Finset (Fin m)) :
    (G.pullback (fun i : Fin m => i.val)).toPredimension.IsStrong
      a (Finset.univ : Finset (Fin m)) ↔
    G.toPredimension.IsStrong
      (a.image (fun i : Fin m => i.val))
      (Finset.range m) := by
  classical
  have hAdj : ∀ i j : Fin m,
      (G.pullback (fun x : Fin m => x.val)).adj i j ↔
        G.adj i.val j.val := by
    intro i j
    rfl
  have h :=
    (G.pullback (fun i : Fin m => i.val)).strong_image_iff G
      (fun i : Fin m => i.val)
      (by
        intro i j hij
        exact Fin.ext hij)
      hAdj a (Finset.univ : Finset (Fin m))
      (Finset.subset_univ _)
  rw [image_fin_val_univ m] at h
  exact h.symm

end GraphOn
end BigHrushovski
