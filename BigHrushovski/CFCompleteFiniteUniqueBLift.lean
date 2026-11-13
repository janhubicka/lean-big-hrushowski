import BigHrushovski.CFArbitraryFiniteUniqueness
import BigHrushovski.CFPrescribedFiniteOrderedLift

/-!
# Finite unique level lifting in the unary b-language

This is the primary finite theorem for the unary presentation.
The R,H compatibility theorem is retained in
`CFCompleteFiniteUniqueLevelLift`; unary clients need not import it.
The theorem statement and proof are unchanged from that module.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every strictly increasing assignment of the FINITELY
represented source birth levels has a unique embedding in
the complete auxiliary b-functional birth language, including
the actual canonical order, reflected level preorder, induced
graph and exact complete unary b-values.

No extension of the level assignment to a globally increasing
map on all natural numbers is assumed. -/
theorem finiteSourcePrescribedLift_existsUnique_orderedB
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃! f : SupportCarrier (Vertex F K) s → Vertex F K,
      Function.Injective f ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        (countableGraph F K).adj x.val y.val ↔
          (countableGraph F K).adj (f x) (f y)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image f =
          birthBValue F K (f x)) ∧
      (∀ x : SupportCarrier (Vertex F K) s,
        (f x).1 = level x.val.1) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        BirthLevelLe F K x.val y.val ↔
          BirthLevelLe F K (f x) (f y)) ∧
      (∀ x y : SupportCarrier (Vertex F K) s,
        canonicalBirthLt F K x.val y.val ↔
          canonicalBirthLt F K (f x) (f y)) := by
  obtain ⟨f, hfInj, hfAdj, hfB, hfBirth, hfLevel, hfOrder⟩ :=
    finiteSourcePrescribedLift_exists_ordered
      F K s hs level hStrict
  refine ⟨f, ⟨hfInj, hfAdj, hfB, hfBirth, hfLevel, hfOrder⟩, ?_⟩
  intro g ⟨hgInj, hgAdj, hgB, hgBirth, hgLevel, hgOrder⟩
  exact arbitraryFiniteEmbedding_unique_of_prescribedLevels
    F K s hs level g f hgInj hfInj hgAdj hfAdj hgB hfB
    hgLevel hfLevel hgOrder hfOrder hgBirth hfBirth

end CFCoherentTower
end BigHrushovski
