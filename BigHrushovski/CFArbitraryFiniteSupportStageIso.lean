import BigHrushovski.CFPartialStageSupportOrder
import BigHrushovski.CFArbitraryFiniteFreshSize

/-!
# Ordered target supports of arbitrary finite C_F embeddings

An arbitrary embedding of a finite closed source in the actual
C_F birth carrier preserves the complete named support of
each new block, rather than merely its cardinality. The
canonical birth order then determines a unique increasing
correspondence between the literal source and target
old-stage support coordinates.

The previous partial-stage order theorem assumed exact
support-image equality as external data. This module derives
that equality from the complete b-value and birth-level
preorder of the arbitrary finite embedding. In particular,
neither a total map of the old finite stage nor a global
increasing map of all natural-number birth levels is used.

The resulting order isomorphism is the old-coordinate
component of the complete local request-code comparison.
Pointwise agreement of its coordinates and the fresh
ordinal component remain separate lemmas.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Every arbitrary finite embedding of a b-closed C_F source
that preserves the full b-values, birth-level preorder and
canonical order induces an order isomorphism from the
literal named old support of each source request to the
literal named old support of its target request.

The empty old support is included. In particular, the target
old stage may be U_0, and no map of the entire old source
stage is required. -/
noncomputable def arbitraryFiniteEmbedding_supportStageIso
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
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    let w : Vertex F K := e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K w.1).carrier :=
      stageLinearOrder F K w.1
    SupportCarrier (stage F K n).carrier r.support ≃o
      SupportCarrier (stage F K w.1).carrier w.2.1.support := by
  classical
  let w : Vertex F K := e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
  have hP : r.support.image (toVertex F K n) ⊆ s := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    rw [← huv]
    exact (hs n r i hi).2 u hu
  have hImage :
      (selectedFiniteSet s
        (r.support.image (toVertex F K n))).image e =
          w.2.1.support.image (toVertex F K w.1) := by
    calc
      (selectedFiniteSet s
        (r.support.image (toVertex F K n))).image e =
          (selectedFiniteSet s
            (birthSupport F K n r)).image e := by
              rw [birthSupport_eq_stageSupport_image]
      _ = birthSupport F K w.1 w.2.1 :=
        (arbitraryFiniteEmbedding_support_block
          F K s e heB heLevel n r i hi).1
      _ = w.2.1.support.image (toVertex F K w.1) :=
        birthSupport_eq_stageSupport_image F K w.1 w.2.1
  exact finiteStageSupportOrderIso F K s
    n w.1 r.support w.2.1.support hP e hImage heOrder

end CFCoherentTower
end BigHrushovski
