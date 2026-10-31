import BigHrushovski.C0TaggedSharedBaseValues
import BigHrushovski.C0TaggedMinimal

/-!
# One-block C₀ functional free amalgamation with both complete values

This packages two independently certified arguments on the *same*
literal tagged free graph. The left factor carries its given canonical
component order; the right factor has its common closed base
frontloaded. Its fresh part is one minimal strong increment.

The common named unary values determine component agreement and
orientation on the base. No matching chronological order on the base
is assumed. The result preserves both *complete vertex-valued* unary
functions, not merely old-neighbour sets. It simultaneously certifies
the full graph, its minimal strong extension over the left factor and
both induced graph embeddings.

For the full finite functional age, the remaining step is to iterate
this theorem through the right factor's fresh component sequence and
to verify the joined finite index at every intermediate prefix.
-/

namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- The exact labelled, two-sided functional one-block bridge.
The right factor's fresh tail is one minimal strong increment.
The shared base's *named* unary values are the only functional
compatibility datum; equal component ranks are not required. -/
theorem taggedOneBlock_twoSidedFunctionalAmalgam
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (F : P → Finset P)
    (hSparseG : G.IsTwoSparse
      (Finset.univ : Finset (Sum P L)))
    (hSparseH : H.IsTwoSparse
      (Finset.univ : Finset (Sum P R)))
    (hBaseStrong : G.toPredimension.IsStrong leftBase
      (Finset.univ : Finset (Sum P L)))
    (hMinimalH : H.toPredimension.IsMinimalStrongStep rightBase
      (Finset.univ : Finset (Sum P R)))
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
    (freeGraph G H).toPredimension.IsMinimalStrongStep
      leftDomain (Finset.univ : Finset (Carrier P L R)) ∧
    (∀ u v : Sum P L,
      (freeGraph G H).adj (leftTag u) (leftTag v) ↔ G.adj u v) ∧
    (∀ u v : Sum P R,
      (freeGraph G H).adj (rightTag u) (rightTag v) ↔ H.adj u v) ∧
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
  obtain ⟨hSparse, hMinimal, hLeft, hRight⟩ :=
    tagged_minimal_strong_free_amalgam
      G H hAgree hSparseG hSparseH hBaseStrong hMinimalH
  obtain ⟨hLeftValues, hRightValues⟩ :=
    taggedCanonicalValues_both_of_named_base
      G H hAgree κL κR F hG hH hFront
  exact ⟨hSparse, hMinimal, hLeft, hRight,
    hLeftValues, hRightValues⟩

end TaggedAmalgam
end BigHrushovski
