import BigHrushovski.InitialSegmentLabels
import BigHrushovski.NatGraphStage

/-!
# Strong graph extensions on gap-free Nat initial segments

An arbitrary finite strong extension A ≤ B can be relabelled over an
old equivalence A ≃ Fin(card A), giving a graph on ℕ supported exactly
on range(card B). The old labels remain unchanged, the new graph is
induced on B and two-sparse, and the old initial segment is strong in
the new initial segment.

Unlike the earlier maximum-plus-one Nat label construction, the
finite domain has no holes. Assembling a coherent sequence of such
stages along the fair request schedule remains a separate task.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {A B : Type*}
variable [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

/-- Relabel a finite strong extension onto a consecutive Nat interval
while fixing the old initial-segment labels. -/
theorem exists_initial_segment_strong_nat_stage
    (K : GraphOn B)
    (i : A → B) (hi : Function.Injective i)
    (hStrong : K.toPredimension.IsStrong
      ((Finset.univ : Finset A).image i)
      (Finset.univ : Finset B))
    (hSparse : K.IsTwoSparse (Finset.univ : Finset B))
    (old : A ≃ Fin (Fintype.card A)) :
    ∃ (new : B ≃ Fin (Fintype.card B)) (N : GraphOn ℕ),
      (∀ a : A, (new (i a)).val = (old a).val) ∧
      (∀ b c : B,
        K.adj b c ↔ N.adj (new b).val (new c).val) ∧
      N.IsTwoSparse (Finset.range (Fintype.card B)) ∧
      N.toPredimension.IsStrong
        (Finset.range (Fintype.card A))
        (Finset.range (Fintype.card B)) ∧
      (∀ x y : ℕ, N.adj x y →
        x ∈ Finset.range (Fintype.card B) ∧
        y ∈ Finset.range (Fintype.card B)) := by
  classical
  let new : B ≃ Fin (Fintype.card B) :=
    extendInitialEquiv i hi old
  let label : B → ℕ := fun b => (new b).val
  have hLabel : Function.Injective label := by
    intro b c h
    exact new.injective (Fin.ext h)
  let N : GraphOn ℕ := K.transportedToNat label hLabel

  have hImageB :
      (Finset.univ : Finset B).image label =
        Finset.range (Fintype.card B) :=
    extendInitialLabels_image i hi old

  have hImageA :
      (((Finset.univ : Finset A).image i).image label) =
        Finset.range (Fintype.card A) := by
    rw [Finset.image_image]
    have hComp : label ∘ i = fun a : A => (old a).val := by
      funext a
      exact extendInitialEquiv_old i hi old a
    rw [hComp]
    ext n
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha⟩
      rw [← ha]
      exact (old a).isLt
    · intro hn
      refine ⟨old.symm ⟨n, hn⟩, ?_⟩
      simp

  have hSparseN : N.IsTwoSparse
      (Finset.range (Fintype.card B)) := by
    have h := K.transportedToNat_sparse label hLabel hSparse
    rw [hImageB] at h
    exact h
  have hStrongN : N.toPredimension.IsStrong
      (Finset.range (Fintype.card A))
      (Finset.range (Fintype.card B)) := by
    have h := K.transportedToNat_strong label hLabel hStrong
    rw [hImageA, hImageB] at h
    exact h

  refine ⟨new, N, ?_, ?_, hSparseN, hStrongN, ?_⟩
  · intro a
    exact extendInitialEquiv_old i hi old a
  · intro b c
    exact K.transportedToNat_induced label hLabel b c
  · intro x y h
    have hh := K.transportedToNat_support label hLabel h
    simpa only [hImageB] using hh

end FiniteSpan
end BigHrushovski
