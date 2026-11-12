import BigHrushovski.CFArbitraryFiniteEmbeddingRigidity

/-!
# Named target supports and blocks under arbitrary finite maps

For the uniqueness induction in the finite C_F lifting lemma,
compare two arbitrary finite maps, not only one constructed lift.

Complete b-values together with reflection of the birth-level
preorder show that every source block maps onto a whole target
block and that its old named support maps onto the exact target
support. These images depend only on the source block, not on
which vertex of that block is chosen.

In particular, if two maps agree on the actual vertices born
before source level n, then their target requests at level n
have exactly the same named old support. This is the support
agreement required by the one-level request-code uniqueness
argument; the fresh-size and ordered adjacency code are
separate obligations.

No map of a complete old source stage is used or assumed.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every fresh vertex of one source birth block has the
same *entire target birth block* under any finite map
preserving complete b-values and reflecting the level
preorder. This is equality of actual finite sets, not
just equality of their cardinalities. -/
theorem arbitraryFiniteEmbedding_sameTargetBlock
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i j : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (hj : (⟨n, ⟨r, j⟩⟩ : Vertex F K) ∈ s) :
    let wi := e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    let wj := e ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩
    birthBlock F K wi.1 wi.2.1 =
      birthBlock F K wj.1 wj.2.1 := by
  have hLeft :=
    (arbitraryFiniteEmbedding_support_block
      F K s e heB heLevel n r i hi).2
  have hRight :=
    (arbitraryFiniteEmbedding_support_block
      F K s e heB heLevel n r j hj).2
  exact hLeft.symm.trans hRight

/-- If two arbitrary finite embeddings agree on all original
source vertices born before n, their target blocks born
from any two vertices of the same source request at level n
have literally the same named old support.

No target-level assignment, whole-stage map or equality of
full request tags is assumed. -/
theorem arbitraryFiniteEmbedding_targetSupport_agree_of_old
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (e g : SupportCarrier (Vertex F K) s → Vertex F K)
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (hgB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image g =
        birthBValue F K (g x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (hgLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (g x) (g y))
    (n : ℕ) (r : BirthRequest F K n)
    (i j : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (hj : (⟨n, ⟨r, j⟩⟩ : Vertex F K) ∈ s)
    (hOld : ∀ x : SupportCarrier (Vertex F K) s,
      x.val.1 < n → e x = g x) :
    let wi := e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    let wj := g ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩
    birthSupport F K wi.1 wi.2.1 =
      birthSupport F K wj.1 wj.2.1 := by
  classical
  let P := selectedFiniteSet s (birthSupport F K n r)
  have hP : P.image e = P.image g := by
    apply Finset.image_congr
    intro x hx
    have hxP : x.val ∈ birthSupport F K n r := by
      simpa [P, selectedFiniteSet] using hx
    exact hOld x (birthSupport_birth_lt F K n r hxP)
  have heSupport :
      P.image e =
        birthSupport F K
          (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).1
          (e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩).2.1 :=
    (arbitraryFiniteEmbedding_support_block
      F K s e heB heLevel n r i hi).1
  have hgSupport :
      P.image g =
        birthSupport F K
          (g ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩).1
          (g ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩).2.1 :=
    (arbitraryFiniteEmbedding_support_block
      F K s g hgB hgLevel n r j hj).1
  exact heSupport.symm.trans (hP.trans hgSupport)

end CFCoherentTower
end BigHrushovski
