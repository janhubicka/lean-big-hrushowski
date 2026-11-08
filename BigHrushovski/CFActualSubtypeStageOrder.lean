import BigHrushovski.CFActualSubtypeRequestOrder
import BigHrushovski.CFSelectedSubtypeOrder
import BigHrushovski.CFSelectedBatchStageOrder

/-!
# Inherited C_F stage order under genuinely partial old-source maps

The actual partial-domain simultaneous batch map preserves the precise
lex order of named supports, fresh sizes and complete adjacency matrices,
followed by fresh ordinals. We identify this order on the two concrete
tagged successor stages with their inherited stageLinearOrder.

No total map from the old source stage to the old target stage is used.
The source selected set S and target stage U_m may be empty, even when
the complete source old stage U_n is not.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The actual partial-old-source C_F selected-batch map preserves
and reflects the recursively inherited finite stage order, even if
the target stage m precedes the source stage n. -/
theorem selectedGrowthBatchMapSubtype_stageOrder_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n m : ℕ)
    (S : Finset (stage F K n).carrier)
    (e : SupportCarrier (stage F K n).carrier S →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (D : Finset (Requests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph S e D)
    (x y : SelectedCarrier (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) S D) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier :=
      stageLinearOrder F K m
    stageLt F K (n + 1)
      (selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D x)
      (selectedSourceMap (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D y) ↔
    stageLt F K (m + 1)
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph S e he D h x)
      (selectedGrowthBatchMapSubtype F K
        (stage F K n).graph (stage F K m).graph S e he D h y) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  have hLex := selectedTargetMapSubtype_taggedLex_iff
    (stage F K n).graph (GrowthAllowedLocal F) (fun P => K P.card)
    (stage F K m).graph (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e he
    (selectedGrowthTagSubtype F K
      (stage F K n).graph (stage F K m).graph S e he D h)
    (selectedGrowthTagSubtype_injective F K
      (stage F K n).graph (stage F K m).graph S e he D h)
    (fun r s => selectedGrowthTagSubtype_order_iff F K
      (stage F K n).graph (stage F K m).graph S e he D h r s)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K
      (stage F K n).graph (stage F K m).graph S e he D h r i)
    (fun r i => selectedGrowthOrdinalIsoSubtype_val F K
      (stage F K n).graph (stage F K m).graph S e he D h r i)
    x y
  exact ((taggedLexLt_stage_iff F K n _ _).symm).trans
    (hLex.trans (taggedLexLt_stage_iff F K m _ _))

end CFCoherentTower
end BigHrushovski
