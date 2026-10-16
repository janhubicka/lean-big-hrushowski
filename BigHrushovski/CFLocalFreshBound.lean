import BigHrushovski.CFMinimalGrowthSize
import BigHrushovski.CFNormalizedLocalType

/-!
# Cardinality of a minimal C_F fresh block over the actual support

The published growth bound applies to the *whole* minimal local
extension P ∪ B, not merely to B. The already certified minimal
growth-size theorem gives |P ∪ B| ≤ K(|P|), provided K satisfies
the numerical inverse domination property.

Here P is a finite subset of the old vertex type S and the
complete graph has carrier S ⊕ B. The old support is present
as P.image Sum.inl and the entire fresh block is the image
of all vertices of B under Sum.inr.

This lemma makes the trivial but important final inequality
|B| ≤ |P ∪ B| explicit, and transports the support cardinality
through any injective old map f:S→U. Consequently the bound
has exactly the form |B| ≤ K(|f[P]|) used by the named
one-step response theorem. No analytic inverse is assumed:
its required numerical property is stated explicitly.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {S B U : Type*}
variable [Fintype S] [DecidableEq S]
variable [Fintype B] [DecidableEq B]
variable [DecidableEq U]

/-- A minimal local C_F extension over P has a fresh block
whose size is bounded by the same conservative inverse
bound for the whole extension, and this bound is unchanged
when P is sent to its literal image by an injective map. -/
theorem minimalLocal_fresh_size_le
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hInverse : ∀ k n : ℕ,
      F n ≤ 2 * (((k + 1 : ℕ) : ℝ)) → n ≤ K k)
    (H : GraphOn (Sum S B))
    (P : Finset S)
    (hMin : H.toPredimension.IsMinimalDClosedStep
      (P.image Sum.inl)
      (P.image Sum.inl ∪ actualFresh S B))
    (hGrowth : H.IsGrowthSparse F Finset.univ)
    (b : B)
    (f : S → U) (hf : Function.Injective f) :
    Fintype.card B ≤ K (P.image f).card := by
  classical
  let A : Finset (Sum S B) := P.image Sum.inl
  let D : Finset (Sum S B) := actualFresh S B
  have hGrowthLocal : H.IsGrowthSparse F (A ∪ D) :=
    H.growthSparse_restrict F hGrowth (Finset.subset_univ _)
  have hxD : Sum.inr b ∈ D :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hxnotA : Sum.inr b ∉ A := by
    intro h
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp h
    cases hs
  have hTotal : (A ∪ D).card ≤ K A.card :=
    H.minimal_growth_extension_card_le F K hInverse
      A (A ∪ D) hMin hGrowthLocal (Sum.inr b)
      (Finset.mem_union_right A hxD) hxnotA
  have hOldCard : A.card = P.card :=
    Finset.card_image_of_injective P Sum.inl_injective
  have hTargetCard : (P.image f).card = P.card :=
    Finset.card_image_of_injective P hf
  have hFreshCard : D.card = Fintype.card B := by
    simp only [D, actualFresh,
      Finset.card_image_of_injective _ Sum.inr_injective]
    simp
  have hFreshSub : D ⊆ A ∪ D :=
    Finset.subset_union_right
  have hBound := (Finset.card_le_card hFreshSub).trans hTotal
  rw [hFreshCard, hOldCard] at hBound
  simpa only [hTargetCard] using hBound

end CFLocalCatalogue
end BigHrushovski
