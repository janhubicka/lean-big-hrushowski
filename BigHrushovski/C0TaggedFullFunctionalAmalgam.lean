import BigHrushovski.C0TaggedMinimalStages
import BigHrushovski.C0TaggedFunctionalOneBlock
import BigHrushovski.C0ClosedBaseFrontload

/-!
# Full finite two-sided C₀ functional free amalgamation

Two arbitrary canonical minimal-component presentations may use
different component orders on their common named closed base. Only
the complete named unary values on that base need to agree.

We retain the complete left witnessing order, frontload the base in
the right witness (preserving every canonical unary value), and
append the right tail. The concrete tagged free graph then has
induced strong copies of both factors, a full minimal-component
presentation, and exact preservation of *both complete* unary
functions. No agreement of numerical base ranks is required.

This is a FINITE age theorem. The countable Fraïssé construction
and identification of its graph reduct with M₀ are independent
obligations, and are not claimed here.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- Both complete named unary values and every nonempty minimal
strong stage are preserved by the actual tagged free graph when
the right named base has already been frontloaded. -/
theorem taggedFunctionalAmalgam_frontloaded
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (F : P → Finset P)
    (hSparseG : G.IsTwoSparse
      (Finset.univ : Finset (Sum P L)))
    (hSparseH : H.IsTwoSparse
      (Finset.univ : Finset (Sum P R)))
    (hLeft : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κL k =
        FiniteC0.oldStage κL (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κL k)
        (FiniteC0.oldStage κL (k+1)))
    (hRight : ∀ j : ℕ, j < m →
      FiniteC0.oldStage κR j =
        FiniteC0.oldStage κR (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κR j)
        (FiniteC0.oldStage κR (j+1)))
    (hG : ∀ p : P,
      FiniteC0.canonicalValue G κL (.inl p) =
        (F p).image (Sum.inl : P → Sum P L))
    (hH : ∀ p : P,
      FiniteC0.canonicalValue H κR (.inl p) =
        (F p).image (Sum.inl : P → Sum P R))
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val) :
    (freeGraph G H).IsTwoSparse
      (Finset.univ : Finset (Carrier P L R)) ∧
    (freeGraph G H).toPredimension.IsStrong
      leftDomain (Finset.univ : Finset (Carrier P L R)) ∧
    (freeGraph G H).toPredimension.IsStrong
      rightDomain (Finset.univ : Finset (Carrier P L R)) ∧
    (∀ k : ℕ, k < n+m →
      FiniteC0.oldStage (joinedIndex κL κR) k =
        FiniteC0.oldStage (joinedIndex κL κR) (k+1) ∨
      (freeGraph G H).toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage (joinedIndex κL κR) k)
        (FiniteC0.oldStage (joinedIndex κL κR) (k+1))) ∧
    (∀ u : Sum P L,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (leftTag u) =
      (FiniteC0.canonicalValue G κL u).image
        (leftTag : Sum P L → Carrier P L R)) ∧
    (∀ u : Sum P R,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (rightTag u) =
      (FiniteC0.canonicalValue H κR u).image
        (rightTag : Sum P R → Carrier P L R)) := by
  have hBaseL := namedBase_strong_of_minimalPresentation
    G κL F hLeft hG
  have hBaseR : H.toPredimension.IsStrong rightBase
      (Finset.univ : Finset (Sum P R)) :=
    namedBase_strong_of_minimalPresentation H κR F hRight hH
  obtain ⟨hSparse, hStrongL, hStrongR, _, _⟩ :=
    tagged_strong_free_amalgam
      G H hAgree hSparseG hSparseH hBaseL hBaseR
  have hJoined :=
    joinedIndex_minimalStages G H hAgree κL κR
      hLeft hRight hFront
  obtain ⟨hValuesL, hValuesR⟩ :=
    taggedCanonicalValues_both_of_named_base
      G H hAgree κL κR F hG hH hFront
  exact ⟨hSparse, hStrongL, hStrongR,
    hJoined, hValuesL, hValuesR⟩

/-- The original presentations need not have their common base
as an initial segment. This constructs a witnessing component
index on their actual free amalgam, keeping the *entire* left
index unchanged. Its right-tail order is the frontloaded right
index. The conclusion gives all induced/strong graph and both
full functional embedding clauses with no frontloading premise. -/
theorem exists_taggedFunctionalAmalgam_of_named_base
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (F : P → Finset P)
    (hSparseG : G.IsTwoSparse
      (Finset.univ : Finset (Sum P L)))
    (hSparseH : H.IsTwoSparse
      (Finset.univ : Finset (Sum P R)))
    (hLeft : ∀ k : ℕ, k < n →
      FiniteC0.oldStage κL k =
        FiniteC0.oldStage κL (k+1) ∨
      G.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κL k)
        (FiniteC0.oldStage κL (k+1)))
    (hRight : ∀ j : ℕ, j < m →
      FiniteC0.oldStage κR j =
        FiniteC0.oldStage κR (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage κR j)
        (FiniteC0.oldStage κR (j+1)))
    (hG : ∀ p : P,
      FiniteC0.canonicalValue G κL (.inl p) =
        (F p).image (Sum.inl : P → Sum P L))
    (hH : ∀ p : P,
      FiniteC0.canonicalValue H κR (.inl p) =
        (F p).image (Sum.inl : P → Sum P R)) :
    ∃ (t : ℕ) (θ : Carrier P L R → Fin t),
      (freeGraph G H).IsTwoSparse
        (Finset.univ : Finset (Carrier P L R)) ∧
      (freeGraph G H).toPredimension.IsStrong
        leftDomain (Finset.univ : Finset (Carrier P L R)) ∧
      (freeGraph G H).toPredimension.IsStrong
        rightDomain (Finset.univ : Finset (Carrier P L R)) ∧
      (∀ k : ℕ, k < t →
        FiniteC0.oldStage θ k = FiniteC0.oldStage θ (k+1) ∨
        (freeGraph G H).toPredimension.IsMinimalStrongStep
          (FiniteC0.oldStage θ k) (FiniteC0.oldStage θ (k+1))) ∧
      (∀ u : Sum P L,
        FiniteC0.canonicalValue (freeGraph G H) θ (leftTag u) =
        (FiniteC0.canonicalValue G κL u).image
          (leftTag : Sum P L → Carrier P L R)) ∧
      (∀ u : Sum P R,
        FiniteC0.canonicalValue (freeGraph G H) θ (rightTag u) =
        (FiniteC0.canonicalValue H κR u).image
          (rightTag : Sum P R → Carrier P L R)) := by
  classical
  let s : Finset (Sum P R) := rightBase
  let ρ : Sum P R → Fin (m+m) :=
    FiniteC0.frontloadIndex κR s
  have hClosed : H.IsClosedUnderValues
      (FiniteC0.canonicalValue H κR) s :=
    namedBase_left_closed H κR F hH
  have hRight' : ∀ j : ℕ, j < m+m →
      FiniteC0.oldStage ρ j = FiniteC0.oldStage ρ (j+1) ∨
      H.toPredimension.IsMinimalStrongStep
        (FiniteC0.oldStage ρ j) (FiniteC0.oldStage ρ (j+1)) :=
    FiniteC0.frontloadIndex_minimal_steps H κR s hClosed hRight
  have hFront : ∀ p : P, ∀ r : R,
      (ρ (.inl p)).val < (ρ (.inr r)).val := by
    intro p r
    have hp : (Sum.inl p : Sum P R) ∈ s :=
      Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
    have hr : (Sum.inr r : Sum P R) ∉ s := by
      intro h
      obtain ⟨q, _, hEq⟩ := Finset.mem_image.mp h
      cases hEq
    change (FiniteC0.frontloadIndex κR s (.inl p)).val <
      (FiniteC0.frontloadIndex κR s (.inr r)).val
    rw [FiniteC0.frontloadIndex_inside κR s (.inl p) hp,
      FiniteC0.frontloadIndex_outside κR s (.inr r) hr]
    have hb := (κR (.inl p)).isLt
    omega
  have hH' : ∀ p : P,
      FiniteC0.canonicalValue H ρ (.inl p) =
        (F p).image (Sum.inl : P → Sum P R) := by
    intro p
    change FiniteC0.canonicalValue H
      (FiniteC0.frontloadIndex κR s) (.inl p) = _
    rw [FiniteC0.canonicalValue_frontload_eq
      H κR s hClosed (.inl p)]
    exact hH p
  obtain ⟨hSparse, hStrongL, hStrongR, hStages, hValL, hValR⟩ :=
    taggedFunctionalAmalgam_frontloaded
      G H hAgree κL ρ F hSparseG hSparseH
      hLeft hRight' hG hH' hFront
  refine ⟨n+(m+m), joinedIndex κL ρ, hSparse, hStrongL,
    hStrongR, hStages, hValL, ?_⟩
  intro u
  calc
    FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL ρ) (rightTag u) =
      (FiniteC0.canonicalValue H ρ u).image
        (rightTag : Sum P R → Carrier P L R) := hValR u
    _ = (FiniteC0.canonicalValue H κR u).image
        (rightTag : Sum P R → Carrier P L R) := by
          rw [FiniteC0.canonicalValue_frontload_eq H κR s hClosed u]

end TaggedAmalgam
end BigHrushovski
