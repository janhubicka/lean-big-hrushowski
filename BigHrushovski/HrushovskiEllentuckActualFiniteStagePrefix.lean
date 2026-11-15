import BigHrushovski.HrushovskiEllentuckActualLevelAction
import BigHrushovski.HrushovskiEllentuckFiniteCutTopology
import BigHrushovski.HrushovskiEllentuckFirstImageLevels

/-!
# Genuine first-n ordered (R,H) image stages as exact supported domains

The two previously certified, independent Track E lemmas assert:
* the image of the literal first n birth stages under an embedding
  with strictly increasing level action h is the part of its range
  whose birth level belongs to h[[0,n)];
* the restriction of the full complete-support domain U[range h]
  to precisely those birth levels is U[h[[0,n)]].

The countable unique-lift/range theorem identifies the range of
*any* genuine named ordered partial (R,H) embedding with U[range h].
This module combines these results for literal vertex sets.

It does not identify the Ellentuck and natural product topologies:
the approximation equality needed for that further comparison is
isolated here without an extra topological axiom.
-/

namespace BigHrushovski.CFCoherentTower

open CFStageCatalogue CFGrowthNumerics

/-- Every genuine ordered (R,H) self-embedding with a specified
strictly increasing level action sends the literal n-stage vertex
domain to the *full generated-support* domain on the first n
image levels. This is an equality of vertex subsets, not just
an equality of the birth levels they represent. -/
theorem orderedRHEmbedding_stageImage_eq_levelPrefix
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (h : ℕ → ℕ) (hh : StrictMono h)
    (f : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedRHEmbedding F K h f)
    (n : ℕ) :
    Set.image f (↑(stageImage F K n) : Set (Vertex F K)) =
      birthLevelDomain F K (Set.image h (Set.Iio n)) := by
  have hb : IsGlobalOrderedBEmbedding F K h f :=
    (isGlobalOrderedBEmbedding_iff_RH F K h f).mpr hf
  obtain ⟨hInj, hAdj, hVal, _, hOrder, hBirth⟩ := hb
  have hRange : Set.range f =
      birthLevelDomain F K (Set.range h) :=
    birthEmbedding_range_eq_levelDomain_of_finite_uniqueness
      F K f h hh hInj hAdj hVal hOrder hBirth
      (singletonClosure_finiteOrderedBEmbedding_unique F K)
  calc
    Set.image f (↑(stageImage F K n) : Set (Vertex F K)) =
        {v : Vertex F K |
          v ∈ Set.range f ∧
          v.1 ∈ Set.image h (Set.Iio n)} :=
      stageImage_under_level_map F K f h hh hBirth n
    _ = {v : Vertex F K |
          v ∈ birthLevelDomain F K (Set.range h) ∧
          v.1 ∈ Set.image h (Set.Iio n)} := by
      rw [hRange]
    _ = birthLevelDomain F K (Set.image h (Set.Iio n)) :=
      (birthLevelDomain_increasing_prefix F K h hh n).symm

/-- A birth-level action need not be supplied as part of the
embedding data. The intrinsic level action extracted from the
named birth-level preorder makes the exact first-n stage formula
hold simultaneously for every n. -/
theorem orderedRHEmbeddingWithoutAction_stageImage_eq_levelPrefix
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (hReq : ∀ n : ℕ, ∃ r : BirthRequest F K n,
      r.support = ∅)
    (f : Vertex F K → Vertex F K)
    (hf : IsGlobalOrderedRHEmbeddingWithoutAction F K f) :
    ∃ h : ℕ → ℕ, StrictMono h ∧
      ∀ n : ℕ,
        Set.image f (↑(stageImage F K n) : Set (Vertex F K)) =
          birthLevelDomain F K (Set.image h (Set.Iio n)) := by
  obtain ⟨h, hh, hfH⟩ :=
    orderedRHEmbedding_has_strict_level_action F K hReq f hf
  exact ⟨h, hh, fun n =>
    orderedRHEmbedding_stageImage_eq_levelPrefix F K h hh f hfH n⟩

end BigHrushovski.CFCoherentTower
