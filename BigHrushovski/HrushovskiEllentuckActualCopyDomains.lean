import BigHrushovski.HrushovskiEllentuckActualCountableRH
import BigHrushovski.HrushovskiEllentuckEmptyRequestWitness
import BigHrushovski.HrushovskiEllentuckFinitaryContinuity

/-!
# Exact copy domains of the countable ordered C_F (R,H) presentation

The unique countable lifting theorem is now available in the
genuine partial (R,H) language, with the birth-level preorder
and canonical order of the manuscript included.

This module identifies, as a literal equality of families of
vertex subsets, the ranges of all such level-labelled embeddings
with the complete-support domains over ranges of strictly
increasing natural-number maps.

It does not assume the existence of singleton-level witnesses
for this equality. Those witnesses are used separately to
recover level-set inclusion from domain inclusion.

The identification concerns copy *domains*. The finite
approximation maps and their Ellentuck topology are further
structure and are not postulated here.
-/

namespace BigHrushovski.CFCoherentTower

/-- Ranges of actual ordered partial (R,H) self-embeddings
with some strictly increasing birth-level action. -/
def ActualOrderedRHCopyDomains
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Set (Set (Vertex F K)) :=
  {D | ∃ h : ℕ → ℕ, StrictMono h ∧
    ∃ f : Vertex F K → Vertex F K,
      IsGlobalOrderedRHEmbedding F K h f ∧
      Set.range f = D}

/-- The synthetic family of complete-support vertex domains
represented by infinite increasing birth-level selections. -/
def SupportedInfiniteLevelDomains
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Set (Set (Vertex F K)) :=
  {D | ∃ h : ℕ → ℕ, StrictMono h ∧
    birthLevelDomain F K (Set.range h) = D}

/-- Every actual global ordered (R,H) self-embedding has the exact
complete-support range. The proof uses the already verified
local finite b-uniqueness theorem and the concrete range criterion,
not an abstract range axiom. -/
theorem actualOrderedRHEmbedding_range_eq_supportDomain
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (f : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedRHEmbedding F K h f) :
    Set.range f = birthLevelDomain F K (Set.range h) := by
  have hb : IsGlobalOrderedBEmbedding F K h f :=
    (isGlobalOrderedBEmbedding_iff_RH F K h f).mpr hf
  obtain ⟨hfInj, hfAdj, hfB, _, hfOrder, hfBirth⟩ := hb
  exact birthEmbedding_range_eq_levelDomain_of_finite_uniqueness
    F K f h hh hfInj hfAdj hfB hfOrder hfBirth
    (singletonClosure_finiteOrderedBEmbedding_unique F K)

/-- Equality of the actual functional copy-domain family with
the finite-support family. The forward direction uses the exact
range theorem for EVERY appropriate global embedding; the reverse
direction uses existence of one genuine global (R,H) lift for
each increasing level action. -/
theorem actualOrderedRHCopyDomains_eq_supported
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    ActualOrderedRHCopyDomains F K =
      SupportedInfiniteLevelDomains F K := by
  ext D
  constructor
  · rintro ⟨h, hh, f, hf, hD⟩
    refine ⟨h, hh, ?_⟩
    exact (actualOrderedRHEmbedding_range_eq_supportDomain
      F K h hh f hf).symm.trans hD
  · rintro ⟨h, hh, hD⟩
    obtain ⟨f, ⟨hf, hRange⟩, _⟩ :=
      existsUnique_globalOrderedRHEmbedding_with_range F K h hh
    exact ⟨h, hh, f, hf, hRange.trans hD⟩

/-- Singleton-support witnesses let one recognize inclusion of
infinite increasing level sets directly from inclusion of the
corresponding genuine functional copy domains. The witnesses
are a genuine hypothesis, not an automatic consequence of
arbitrary numerical parameters F,K. -/
theorem actualOrderedRHCopyDomain_subset_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (h k : ℕ → ℕ) :
    birthLevelDomain F K (Set.range h) ⊆
      birthLevelDomain F K (Set.range k) ↔
      Set.range h ⊆ Set.range k :=
  birthLevelDomain_subset_iff_of_empty_requests F K hReq
    (Set.range h) (Set.range k)

end BigHrushovski.CFCoherentTower
