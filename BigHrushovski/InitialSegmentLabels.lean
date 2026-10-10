import BigHrushovski.NatGraphStage
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# Gap-free labels for finite strong successor stages

The earlier `extendNatLabels` preserves arbitrary finite old labels, but
may introduce permanent gaps in a chain on the ambient carrier ℕ. Here
an old finite stage is assumed to occupy the first `card A` natural
numbers. We construct a bijective enumeration of every finite extension
whose first `card A` labels are *exactly* the old ones.

This is a carrier lemma: it does not construct fair strong amalgamation
responses or the countable generic graph.
-/

namespace BigHrushovski
namespace FiniteSpan

variable {A B : Type*}
variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A finite extension splits into the old carrier and its fresh tail.
The cardinality equality gives the new endpoint of the initial segment. -/
private theorem initialSegment_card
    (f : A → B) (hf : Function.Injective f) :
    Fintype.card A + Fintype.card (Tail f) = Fintype.card B := by
  classical
  simpa only [Fintype.card_sum] using
    (Fintype.card_congr (splitEquiv f hf))

/-- An enumeration of B by the initial segment `Fin (card B)`
extending the old enumeration of A by `Fin (card A)`.
Every fresh vertex is labelled after every old vertex, with no gaps. -/
noncomputable def extendInitialEquiv
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) :
    B ≃ Fin (Fintype.card B) :=
  (((splitEquiv f hf).symm.trans
      (Equiv.sumCongr old (Fintype.equivFin (Tail f)))).trans
      finSumFinEquiv).trans (finCongr (initialSegment_card f hf))

/-- The new equivalence preserves every old natural-number label. -/
theorem extendInitialEquiv_old
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) (a : A) :
    (extendInitialEquiv f hf old (f a)).val = (old a).val := by
  classical
  have hpre : (splitEquiv f hf).symm (f a) = Sum.inl a := by
    apply (splitEquiv f hf).injective
    simp
  simp [extendInitialEquiv, hpre]

/-- The same labels as a map into the common Nat carrier. -/
noncomputable def extendInitialLabels
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) : B → ℕ :=
  fun b => (extendInitialEquiv f hf old b).val

theorem extendInitialLabels_old
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) (a : A) :
    extendInitialLabels f hf old (f a) = (old a).val :=
  extendInitialEquiv_old f hf old a

theorem extendInitialLabels_injective
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) :
    Function.Injective (extendInitialLabels f hf old) := by
  intro b c h
  apply (extendInitialEquiv f hf old).injective
  exact Fin.ext h

/-- Unlike the earlier unrestricted fresh-label map, the new labelled
domain is *exactly* the consecutive interval [0, card B). -/
theorem extendInitialLabels_image
    (f : A → B) (hf : Function.Injective f)
    (old : A ≃ Fin (Fintype.card A)) :
    (Finset.univ : Finset B).image (extendInitialLabels f hf old) =
      Finset.range (Fintype.card B) := by
  classical
  ext n
  simp only [Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [← hb]
    exact (extendInitialEquiv f hf old b).isLt
  · intro hn
    refine ⟨(extendInitialEquiv f hf old).symm ⟨n, hn⟩, ?_⟩
    simp [extendInitialLabels]

end FiniteSpan
end BigHrushovski
