import BigHrushovski.CFFiniteRHIntrinsicLevelClassification
import BigHrushovski.CFPartialOrderedBComposition
import BigHrushovski.CFPrescribedFiniteRHRestriction

/-!
# Restriction and composition of arbitrary finite C_F R/H embeddings

The finite lifting theorem constructs a canonical embedding from
an assignment of the finitely represented levels. To apply it
directly to finite substructures one also needs to know that
arbitrary embeddings (not only chosen canonical lifts) compose
and restrict in the genuine functional language.

For composition we translate each partial R/H embedding to
exact complete b-values, compose two maps defined only on
their literal finite sources, and apply finite uniqueness to
identify the composite with an actual prescribed R/H lift.
For restriction we use intrinsic-level recognition of the
arbitrary original embedding and the exact restriction identity
of prescribed lifts.

Both arguments retain all defined H-values and reflection of
the domain of the partial operation H, and require no total
finite-stage map or global increasing map of all birth levels.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The composition of two arbitrary genuinely partial finite
ordered R/H embeddings is again an embedding of the actual
finite R/H language. The second domain is the *literal image*
of the first, which is R/H-closed by finite image closure.

Both constituent maps preserve and reflect the graph, the
birth-level preorder and canonical order, all complete
R-values, and all defined H-values with H-domain reflection.
The intrinsic target-level assignment of the composite is
recovered from the composite itself. -/
theorem arbitraryFiniteRHEmbedding_comp
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (g : SupportCarrier (Vertex F K)
      (finiteBirthSourceImage F K s e) → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (heRH : FiniteSourceRHValues F K s e)
    (hgInj : Function.Injective g)
    (hgAdj : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      (countableGraph F K).adj u.val v.val ↔
        (countableGraph F K).adj (g u) (g v))
    (hgLevel : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      BirthLevelLe F K u.val v.val ↔
        BirthLevelLe F K (g u) (g v))
    (hgOrder : ∀ u v : SupportCarrier (Vertex F K)
        (finiteBirthSourceImage F K s e),
      canonicalBirthLt F K u.val v.val ↔
        canonicalBirthLt F K (g u) (g v))
    (hgRH : FiniteSourceRHValues F K
      (finiteBirthSourceImage F K s e) g) :
    let c := fun x : SupportCarrier (Vertex F K) s =>
      g (finiteBirthSourceImagePoint F K s e x)
    FiniteRHLevelEmbedding F K s
      (finiteEmbeddingLevelMap F K s c) c := by
  let t := finiteBirthSourceImage F K s e
  let j := finiteBirthSourceImagePoint F K s e
  let c : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => g (j x)
  have hsB : IsBirthBlockClosed F K s :=
    (finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH
  have heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x) :=
    arbitraryFiniteRHEmbedding_completeB
      F K s hsB e heInj heAdj heLevel heOrder heRH
  have htB : IsBirthBlockClosed F K t :=
    finiteBirthSourceImage_bClosed F K s e heB
  have hgB : ∀ y : SupportCarrier (Vertex F K) t,
      (finiteSourceBirthBValue F K t y).image g =
        birthBValue F K (g y) :=
    arbitraryFiniteRHEmbedding_completeB
      F K t htB g hgInj hgAdj hgLevel hgOrder hgRH
  obtain ⟨hcInj, hcAdj, hcB, hcLevel, hcOrder⟩ :=
    finiteBirthSourceImage_comp_orderedB
      F K s e g heInj heAdj heB heLevel heOrder
      hgInj hgAdj hgB hgLevel hgOrder
  let level := finiteEmbeddingLevelMap F K s c
  have hStrict : StrictOnRepresented F K s level :=
    finiteEmbeddingLevelMap_strictOnRepresented
      F K s c hcLevel
  have hcBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (c x).1 = level x.val.1 :=
    finiteEmbeddingLevelMap_exact F K s c hcLevel
  obtain ⟨n, hCover⟩ := finiteSet_covered F K s
  have hcCanonical : c =
      finiteSourcePrescribedLift F K s hsB level hStrict n hCover :=
    finiteBirthSourceImage_comp_eq_prescribedLift
      F K s hsB e g heInj heAdj heB heLevel heOrder
      hgInj hgAdj hgB hgLevel hgOrder
      level hStrict hcBirth n hCover
  have hcRH : FiniteSourceRHValues F K s c := by
    rw [hcCanonical]
    exact finiteSourcePrescribedLift_has_RHValues
      F K s hsB level hStrict n hCover
  exact ⟨hcInj, hcAdj, hcBirth, hcLevel, hcOrder, hcRH⟩

/-- Restrict an ARBITRARY finite R/H embedding to any smaller
finite R/H-closed substructure. This does not require the
original map to have been chosen by the canonical recursion.

The restricted map preserves the entire actual partial
functional language, including reflection of H's domain. -/
theorem arbitraryFiniteRHEmbedding_restrict
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s t : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (htRH : IsFiniteRHClosed F K t)
    (hst : s ⊆ t)
    (e : SupportCarrier (Vertex F K) t → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) t,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) t,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) t,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (heRH : FiniteSourceRHValues F K t e) :
    let r := fun x : SupportCarrier (Vertex F K) s =>
      e (finiteClosedSourceInclusion F K s t hst x)
    FiniteRHLevelEmbedding F K s
      (finiteEmbeddingLevelMap F K s r) r := by
  let i := finiteClosedSourceInclusion F K s t hst
  let r : SupportCarrier (Vertex F K) s → Vertex F K :=
    fun x => e (i x)
  let levelT := finiteEmbeddingLevelMap F K t e
  let hStrictT : StrictOnRepresented F K t levelT :=
    finiteEmbeddingLevelMap_strictOnRepresented F K t e heLevel
  have hsB : IsBirthBlockClosed F K s :=
    (finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH
  have htB : IsBirthBlockClosed F K t :=
    (finiteRHClosed_iff_birthBlockClosed F K t).mp htRH
  obtain ⟨nS, hCoverS⟩ := finiteSet_covered F K s
  obtain ⟨nT, hCoverT⟩ := finiteSet_covered F K t
  have heCanonical : e =
      finiteSourcePrescribedLift F K t htB levelT hStrictT nT hCoverT :=
    finiteRHEmbedding_eq_prescribed_of_intrinsicLevels
      F K t htRH e heInj heAdj heLevel heOrder heRH nT hCoverT
  have hrInj : Function.Injective r := by
    intro x y hxy
    exact finiteClosedSourceInclusion_injective F K s t hst
      (heInj hxy)
  have hrAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (r x) (r y) := by
    intro x y
    exact heAdj (i x) (i y)
  have hrLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (r x) (r y) := by
    intro x y
    exact heLevel (i x) (i y)
  have hrOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (r x) (r y) := by
    intro x y
    exact heOrder (i x) (i y)
  have hrRH : FiniteSourceRHValues F K s r := by
    dsimp only [r]
    rw [heCanonical]
    exact finiteSourcePrescribedLift_restriction_RHValues
      F K s t hsB htB hst levelT hStrictT
      nS nT hCoverS hCoverT
  have hrBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (r x).1 =
        finiteEmbeddingLevelMap F K s r x.val.1 :=
    finiteEmbeddingLevelMap_exact F K s r hrLevel
  exact ⟨hrInj, hrAdj, hrBirth, hrLevel, hrOrder, hrRH⟩

end CFCoherentTower
end BigHrushovski
