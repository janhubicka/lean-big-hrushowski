import BigHrushovski.CFFiniteRHClosedLevelLifting

/-!
# The intrinsic level assignment of finite R/H-embeddings

The finite unique-lifting theorem is normally stated with a
prescribed map on the represented source birth levels. Here
we remove that prescription from the *recognition* direction:
an arbitrary ordered embedding of a finite R/H-substructure
determines its own strictly increasing represented-level map,
and is exactly the prescribed finite lift for that map.

The chosen stage cover in the canonical finite construction is
arbitrary. This result proves finite recognition; it does not
construct or classify any global countable self-embedding.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Package the already certified properties of the particular
canonical lift as an embedding in the real finite R/H language.
Complete R-values, defined H-values and H-domain reflection
are included; no auxiliary b-value preservation is substituted
for the functional language. -/
theorem finiteSourcePrescribedLift_is_finiteRHLevelEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsB : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level)
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    FiniteRHLevelEmbedding F K s level
      (finiteSourcePrescribedLift F K s hsB level hStrict n hCover) := by
  obtain ⟨hInj, hAdj, _, hBirth, hLevel, hOrder⟩ :=
    finiteSourcePrescribedLift_orderedB_properties
      F K s hsB level hStrict n hCover
  exact ⟨hInj, hAdj, hBirth, hLevel, hOrder,
    finiteSourcePrescribedLift_has_RHValues
      F K s hsB level hStrict n hCover⟩

/-- Every arbitrary finite ordered R/H-embedding of a genuine
finite R/H-substructure is LITERALLY the canonical finite
prescribed lift for its own intrinsic represented-level map.

The map is extracted from the given embedding, not chosen
independently. Its strictness is proved from preservation and
reflection of the level preorder. The statement allows empty
sources, gaps at any level, and arbitrary source stage covers.
No globally increasing map of all of omega is assumed. -/
theorem finiteRHEmbedding_eq_prescribed_of_intrinsicLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
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
    (n : ℕ) (hCover : s ⊆ stageImage F K n) :
    e = finiteSourcePrescribedLift F K s
      ((finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH)
      (finiteEmbeddingLevelMap F K s e)
      (finiteEmbeddingLevelMap_strictOnRepresented F K s e heLevel)
      n hCover := by
  let level := finiteEmbeddingLevelMap F K s e
  let hStrict : StrictOnRepresented F K s level :=
    finiteEmbeddingLevelMap_strictOnRepresented F K s e heLevel
  let hsB : IsBirthBlockClosed F K s :=
    (finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH
  have heBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1 := by
    intro x
    exact finiteEmbeddingLevelMap_exact F K s e heLevel x
  have he : FiniteRHLevelEmbedding F K s level e :=
    ⟨heInj, heAdj, heBirth, heLevel, heOrder, heRH⟩
  have hCanonical : FiniteRHLevelEmbedding F K s level
      (finiteSourcePrescribedLift F K s hsB level hStrict n hCover) :=
    finiteSourcePrescribedLift_is_finiteRHLevelEmbedding
      F K s hsB level hStrict n hCover
  obtain ⟨f, hf, hUnique⟩ :=
    finiteRHClosed_existsUnique_levelLift
      F K s hsRH level hStrict
  exact (hUnique e he).trans
    (hUnique
      (finiteSourcePrescribedLift F K s hsB level hStrict n hCover)
      hCanonical).symm

end CFCoherentTower
end BigHrushovski
