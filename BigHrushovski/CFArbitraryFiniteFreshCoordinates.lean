import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity
import BigHrushovski.CFArbitraryFiniteTargetSupportAgreement

/-!
# Exact fresh-coordinate images of arbitrary finite C_F embeddings

An arbitrary finite complete-b embedding maps the whole source
fresh birth block onto the whole target block. Consequently
each source fresh ordinal has an image carrying the *same*
target request tag; the induced canonical birth order fixes
its ordinal value exactly.

We package these two previously verified facts together. This
is the fresh half of the ordered local coordinate comparison
required for uniqueness of finite level lifts.

The hypotheses concern only the finite b-closed source subtype.
There is no map of the full source old stage or a global
self-embedding of the countable birth carrier.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Let the image of one vertex of a complete source block
have birth level m and literal target request t. Then the
image of every other vertex of the SAME source block has
the SAME level and request tag, and the EXACT same ordinal
value as its source.

No preselected target tag, fresh-size equality or block
surjectivity is assumed: complete b-values and the level
preorder supply the block image, and canonical order
rigidity supplies the ordinal. -/
theorem arbitraryFiniteEmbedding_freshCoordinate
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (j : Fin r.code.1.val)
    (hj : (⟨n, ⟨r, j⟩⟩ : Vertex F K) ∈ s) :
    let w : Vertex F K :=
      e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    ∃ k : Fin w.2.1.code.1.val,
      e ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩ =
        (⟨w.1, ⟨w.2.1, k⟩⟩ : Vertex F K) ∧
      k.val = j.val := by
  classical
  let vi : Vertex F K := ⟨n, ⟨r, i⟩⟩
  let vj : Vertex F K := ⟨n, ⟨r, j⟩⟩
  let w : Vertex F K := e ⟨vi, hi⟩
  have hImage :
      (selectedFiniteSet s (birthBlock F K n r)).image e =
        birthBlock F K w.1 w.2.1 :=
    (arbitraryFiniteEmbedding_support_block
      F K s e heB heLevel n r i hi).2
  have hjBlock : vj ∈ birthBlock F K n r :=
    birthFresh_mem_block F K n r j
  have hjSelected :
      (⟨vj, hj⟩ : SupportCarrier (Vertex F K) s) ∈
        selectedFiniteSet s (birthBlock F K n r) := by
    simpa [selectedFiniteSet] using hjBlock
  have hTarget :
      e ⟨vj, hj⟩ ∈ birthBlock F K w.1 w.2.1 := by
    rw [← hImage]
    exact Finset.mem_image.mpr
      ⟨⟨vj, hj⟩, hjSelected, rfl⟩
  obtain ⟨k, hk⟩ :=
    (mem_birthBlock_iff_exists_ordinal F K w.1 w.2.1 _).mp hTarget
  have hOrdinal :=
    arbitraryFiniteEmbedding_birthOrdinal
      F K s hs e heB heLevel heOrder
      (⟨vj, hj⟩ : SupportCarrier (Vertex F K) s)
  rw [hk] at hOrdinal
  refine ⟨k, hk, ?_⟩
  simpa [birthOrdinal] using hOrdinal

end CFCoherentTower
end BigHrushovski
