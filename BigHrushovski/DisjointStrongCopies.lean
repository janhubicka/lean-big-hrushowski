import BigHrushovski.SpanNormalization
import BigHrushovski.UnlabelledExtension
import BigHrushovski.GlobalClosure

/-!
# Strong copies over a closed base avoiding a prescribed finite set

Let C ⊆ B be finite globally strong subgraphs of a countable
two-sparse graph M with the strong extension property. For any
finite two-sparse graph D containing an induced strong copy of C,
there is a globally strong induced copy of D in M over C whose
vertices outside C avoid B.

The construction strongly freely amalgamates B and D over C,
then uses the strong extension property of M to realize the
amalgam over the literal copy of B already inside M. Exactness of
the tagged amalgam ensures there are no identifications outside C.

This is the key finite step in constructing arbitrarily many
disjoint conjugates over a strong closure. It does not yet state
anything about first-order algebraic closure or automorphism
orbits.
-/

namespace BigHrushovski
namespace FiniteCatalogue

private theorem subtype_univ_image_val (s : Finset ℕ) :
    (Finset.univ : Finset {v : ℕ // v ∈ s}).image Subtype.val = s := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact v.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Given a strong finite extension D of a finite strong base C,
a globally strong copy of D can be placed over C while avoiding
any preassigned finite globally strong B ⊇ C outside C. -/
theorem exists_disjoint_strong_copy
    (M : GraphOn ℕ)
    (hSparseM : ∀ s : Finset ℕ, 0 ≤ M.predim s)
    (hExtM : HasStrongExtensionProperty M)
    (c b : Finset ℕ) (hcb : c ⊆ b)
    (hc : M.toPredimension.IsGloballyStrong c)
    (hb : M.toPredimension.IsGloballyStrong b)
    {D : Type*} [Fintype D] [DecidableEq D]
    (H : GraphOn D)
    (j : {p : ℕ // p ∈ c} → D)
    (hj : Function.Injective j)
    (hBaseInduced : ∀ p q : {p : ℕ // p ∈ c},
      H.adj (j p) (j q) ↔ M.adj p.val q.val)
    (hSparseH : H.IsTwoSparse (Finset.univ : Finset D))
    (hStrongH : H.toPredimension.IsStrong
      ((Finset.univ : Finset {p : ℕ // p ∈ c}).image j)
      (Finset.univ : Finset D)) :
    ∃ g : D → ℕ,
      Function.Injective g ∧
      (∀ x y : D, H.adj x y ↔ M.adj (g x) (g y)) ∧
      (∀ p : {p : ℕ // p ∈ c}, g (j p) = p.val) ∧
      M.toPredimension.IsGloballyStrong
        ((Finset.univ : Finset D).image g) ∧
      (∀ x : D, g x ∈ b →
        ∃ p : {p : ℕ // p ∈ c}, x = j p) := by
  classical
  let P := {p : ℕ // p ∈ c}
  let A := {v : ℕ // v ∈ b}
  let G : GraphOn A := M.pullback (Subtype.val : A → ℕ)
  let i : P → A := fun p => ⟨p.val, hcb p.property⟩
  have hi : Function.Injective i := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (Subtype.val : A → ℕ) hpq
  have hAgree : ∀ p q : P,
      G.adj (i p) (i q) ↔ H.adj (j p) (j q) := by
    intro p q
    exact (hBaseInduced p q).symm
  have hSparseG : G.IsTwoSparse (Finset.univ : Finset A) := by
    have h := G.twoSparse_image_iff M
      (Subtype.val : A → ℕ)
      Subtype.val_injective (fun _ _ => Iff.rfl)
      (Finset.univ : Finset A)
    rw [subtype_univ_image_val b] at h
    exact h.mp (by intro s _; exact hSparseM s)
  have hImageI :
      (((Finset.univ : Finset P).image i).image
        (Subtype.val : A → ℕ)) = c := by
    rw [Finset.image_image]
    have hComp :
        (Subtype.val : A → ℕ) ∘ i =
          (Subtype.val : P → ℕ) := by
      funext p
      rfl
    rw [hComp]
    exact subtype_univ_image_val c
  have hStrongG : G.toPredimension.IsStrong
      ((Finset.univ : Finset P).image i)
      (Finset.univ : Finset A) := by
    have h := (G.strong_image_iff M
      (Subtype.val : A → ℕ)
      Subtype.val_injective (fun _ _ => Iff.rfl)
      ((Finset.univ : Finset P).image i)
      (Finset.univ : Finset A)
      (Finset.subset_univ _)).mp (by
        rw [hImageI, subtype_univ_image_val b]
        exact hc b hcb)
    exact h
  obtain ⟨K, left, right, hLeft, hRight, hAdjLeft,
      hAdjRight, hAgreement, hOnlyBase,
      hSparseK, hStrongLeft, hStrongRight⟩ :=
    FiniteSpan.exists_finite_strong_free_amalgam
      G H i j hi hj hAgree hSparseG hSparseH
      hStrongG hStrongH
  have hGlobalA : M.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset A).image
        (Subtype.val : A → ℕ)) := by
    rw [subtype_univ_image_val b]
    exact hb
  obtain ⟨k, hk, hAdjK, hFixA, hGlobalK⟩ :=
    arbitrary_finite_strong_extension M hExtM
      G K left hLeft (fun x y => (hAdjLeft x y).symm)
      hSparseG hSparseK hStrongLeft
      (Subtype.val : A → ℕ) Subtype.val_injective
      (fun _ _ => Iff.rfl) hGlobalA
  let g : D → ℕ := k ∘ right
  have hgInj : Function.Injective g := hk.comp hRight
  have hAdjG : ∀ x y : D,
      H.adj x y ↔ M.adj (g x) (g y) := by
    intro x y
    exact (hAdjRight x y).symm.trans (hAdjK (right x) (right y))
  have hFixC : ∀ p : P, g (j p) = p.val := by
    intro p
    calc
      g (j p) = k (right (j p)) := rfl
      _ = k (left (i p)) := congrArg k (hAgreement p).symm
      _ = (i p).val := hFixA (i p)
      _ = p.val := rfl
  have hGlobG : M.toPredimension.IsGloballyStrong
      ((Finset.univ : Finset D).image g) := by
    have hLocal :=
      (K.strong_image_iff M k hk hAdjK
        ((Finset.univ : Finset D).image right)
        (Finset.univ : Finset _)
        (Finset.subset_univ _)).mpr hStrongRight
    have hStrongImage :=
      M.toPredimension.globallyStrong_of_strong_in_global
        hLocal hGlobalK
    simpa only [Finset.image_image] using hStrongImage
  have hAvoid (x : D) (hx : g x ∈ b) :
      ∃ p : P, x = j p := by
    let a : A := ⟨g x, hx⟩
    have hEq : k (left a) = k (right x) := by
      calc
        k (left a) = a.val := hFixA a
        _ = g x := rfl
        _ = k (right x) := rfl
    obtain ⟨p, _, hp⟩ := hOnlyBase a x (hk hEq)
    exact ⟨p, hp⟩
  exact ⟨g, hgInj, hAdjG, hFixC, hGlobG, hAvoid⟩

end FiniteCatalogue
end BigHrushovski
