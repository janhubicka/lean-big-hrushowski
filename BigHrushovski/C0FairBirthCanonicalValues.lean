import BigHrushovski.C0FairComponentBirthIndex
import BigHrushovski.C0LowerRespectingOrderInvariance

/-!
# Track A: complete canonical values for the fair birth-component order

Fix a finite fair prefix Q_n and an arbitrary finite canonical C₀
presentation of its induced graph whose complete values agree
literally with the original unary function C. The intrinsic fair
birth indices retain exactly the same component classes and
place every strict lower component earlier. The existing finite
invariance theorem then shows that the entire canonical value
under the fair birth index is exactly C(x).

No specific numerical index of the comparison presentation is
required; indices with empty levels are allowed. The remaining
countable step is to obtain the comparison presentation on each
literal closed Q_n from an ambient cofinal finite canonical stage.
-/

namespace BigHrushovski
namespace FiniteC0

/-- The graph induced on the *literal* n-th fair prefix. -/
def fairPrefixGraph
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (hC : IsCompleteUnaryClosure C) (n : ℕ) :
    GraphOn {v : ℕ // v ∈ fairComponentPrefix C hC n} :=
  N.pullback (Subtype.val :
    {v : ℕ // v ∈ fairComponentPrefix C hC n} → ℕ)

/-- An arbitrary finite canonical index on a literal fair prefix
may be replaced by the intrinsic birth index without changing
the complete vertex-valued unary operation. Incomparable
components may be reordered freely. -/
theorem fairBirthIndex_preserves_complete_canonicalValue
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (hC : IsCompleteUnaryClosure C) (n : ℕ)
    {m : ℕ}
    (κ : {v : ℕ // v ∈ fairComponentPrefix C hC n} → Fin m)
    (hValues :
      ∀ v : {w : ℕ // w ∈ fairComponentPrefix C hC n},
      C v.val =
        (canonicalValue (fairPrefixGraph N C hC n) κ v).image
          (Subtype.val :
            {w : ℕ // w ∈ fairComponentPrefix C hC n} → ℕ))
    (x : {w : ℕ // w ∈ fairComponentPrefix C hC n}) :
    (canonicalValue (fairPrefixGraph N C hC n)
      (fairComponentBirthIndex C hC n) x).image
        (Subtype.val :
          {w : ℕ // w ∈ fairComponentPrefix C hC n} → ℕ) =
      C x.val := by
  classical
  let T := {v : ℕ // v ∈ fairComponentPrefix C hC n}
  let H : GraphOn T := fairPrefixGraph N C hC n
  let β : T → Fin n := fairComponentBirthIndex C hC n
  have hOldIndex : ∀ u v : T, κ u = κ v ↔ C u.val = C v.val := by
    intro u v
    constructor
    · intro heq
      have hCanon :
          canonicalValue H κ u = canonicalValue H κ v :=
        (canonicalValue_eq_iff_index_eq H κ u v).mpr heq
      calc
        C u.val = (canonicalValue H κ u).image
            (Subtype.val : T → ℕ) := hValues u
        _ = (canonicalValue H κ v).image
            (Subtype.val : T → ℕ) := by rw [hCanon]
        _ = C v.val := (hValues v).symm
    · intro hEq
      apply (canonicalValue_eq_iff_index_eq H κ u v).mp
      apply Finset.image_injective
        (Subtype.val_injective :
          Function.Injective (Subtype.val : T → ℕ))
      calc
        (canonicalValue H κ u).image
            (Subtype.val : T → ℕ) = C u.val := (hValues u).symm
        _ = C v.val := hEq
        _ = (canonicalValue H κ v).image
            (Subtype.val : T → ℕ) := hValues v
  have hComponents : ∀ u v : T, κ u = κ v ↔ β u = β v := by
    intro u v
    exact (hOldIndex u v).trans
      (fairComponentBirthIndex_eq_iff_value_eq C hC n u v).symm
  have hLowerEarlier : ∀ u v : T, κ u ≠ κ v →
      v ∈ canonicalValue H κ u → (β v).val < (β u).val := by
    intro u v hDiff hv
    have hIn : v.val ∈ C u.val := by
      rw [hValues u]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hValueDifferent : C v.val ≠ C u.val := by
      intro heq
      exact hDiff ((hOldIndex u v).mpr heq.symm)
    exact fairComponentBirthIndex_lower_earlier
      C hC n u v hIn hValueDifferent
  have hCanonical :
      canonicalValue H κ x = canonicalValue H β x :=
    canonicalValue_eq_of_lower_respecting_order
      H κ β hComponents hLowerEarlier x
  calc
    (canonicalValue H β x).image (Subtype.val : T → ℕ) =
        (canonicalValue H κ x).image (Subtype.val : T → ℕ) :=
      congrArg (fun s : Finset T =>
        s.image (Subtype.val : T → ℕ)) hCanonical.symm
    _ = C x.val := (hValues x).symm

end FiniteC0
end BigHrushovski
