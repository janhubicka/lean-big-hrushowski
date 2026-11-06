import BigHrushovski.CFBirthBValues
import BigHrushovski.CFSelectedSubtypeBValues
import BigHrushovski.CFActualSubtypeStageOrder

/-!
# Complete birth b-values of selected fresh C_F vertices

A one-level selected carrier has an auxiliary b-value for each fresh
vertex: its entire named old support and every ordinal of its fresh
block.  This is not merely a list of graph neighbours.

The actual countable birth-labelled presentation has a separate
definition, birthBValue.  These two finite sets agree LITERALLY
after the selected source inclusion and its canonical birth map.
Likewise the actual partial-domain simultaneous target map sends
the source selected b-value ONTO the complete birth value of the
target fresh vertex.

The old-vertex part remains the induction hypothesis, to be
transported via the canonical stage ascent.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The complete selected fresh b-value, under the literal source
inclusion, is exactly the old tagged support plus the WHOLE fresh
block of the original request. -/
theorem selectedBlockBValue_sourceImage
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U)
    (D : Finset (Requests G Allowed bound))
    (r : SelectedRequests G Allowed bound D)
    (hSub : r.val.support ⊆ S) :
    (selectedBlockBValue G Allowed bound S D r hSub).image
      (selectedSourceMap G Allowed bound S D) =
    taggedSupport G Allowed bound r.val ∪
      taggedBlock G Allowed bound r.val := by
  classical
  have h := selectedBlockBValue_image
    G Allowed bound G Allowed bound S D
    (fun u : U => u)
    (fun r : SelectedRequests G Allowed bound D => r.val)
    (fun r i => i) r hSub
    (by simp)
    (fun j => ⟨j, rfl⟩)
  simpa only [selectedSourceMap, selectedTargetMap] using h

end CFStageCatalogue

namespace CFCoherentTower

open CFStageCatalogue

/-- A selected new vertex has exactly its actual complete
birth-b-value: no support vertex and no fresh ordinal is missing.
The comparison uses the literal source stage inclusion, not a
separately chosen copy of the selected graph. -/
theorem selectedFresh_birthBValue_source
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (S : Finset (stage F K n).carrier)
    (D : Finset (BirthRequest F K n))
    (r : SelectedRequests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) D)
    (hSub : r.val.support ⊆ S)
    (i : Fin r.val.code.1.val) :
    birthBValue F K (⟨n, ⟨r.val, i⟩⟩ : Vertex F K) =
      (selectedBlockBValue (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        S D r hSub).image
          (fun z =>
            toVertex F K (n + 1)
              (selectedSourceMap (stage F K n).graph
                (GrowthAllowedLocal F) (fun P => K P.card)
                S D z)) := by
  classical
  have hImage := selectedBlockBValue_sourceImage
    (stage F K n).graph (GrowthAllowedLocal F)
    (fun P => K P.card) S D r hSub
  calc
    birthBValue F K (⟨n, ⟨r.val, i⟩⟩ : Vertex F K) =
      (taggedSupport (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r.val ∪
       taggedBlock (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r.val).image
          (toVertex F K (n + 1)) := by
          rw [birthBValue_of_fresh]
          simp only [birthSupport, birthBlock, Finset.image_union]
    _ = ((selectedBlockBValue (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        S D r hSub).image
          (selectedSourceMap (stage F K n).graph
            (GrowthAllowedLocal F) (fun P => K P.card)
            S D)).image (toVertex F K (n + 1)) := by
          rw [hImage]
    _ = _ := by
      rw [Finset.image_image]
      rfl

/-- For any genuine partial old-source map and constructed target
request, the complete birth-b-value of the target fresh vertex
is exactly the image of the source SELECTED support-plus-whole-block
value under the single simultaneous map and target birth embedding. -/
theorem selectedFresh_birthBValue_target
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
    (D : Finset (BirthRequest F K n))
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph S e D)
    (r : SelectedRequests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) D)
    (i : Fin r.val.code.1.val) :
    birthBValue F K
      (⟨m, ⟨selectedGrowthTagSubtype F K
          (stage F K n).graph (stage F K m).graph S e he D h r,
        selectedGrowthOrdinalIsoSubtype F K
          (stage F K n).graph (stage F K m).graph S e he D h r i⟩⟩ :
        Vertex F K) =
      (selectedBlockBValue (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        S D r (h.supports r.val r.property)).image
        (fun z =>
          toVertex F K (m + 1)
            (selectedGrowthBatchMapSubtype F K
              (stage F K n).graph (stage F K m).graph
              S e he D h z)) := by
  classical
  letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier := stageLinearOrder F K m
  let target := selectedGrowthTagSubtype F K
    (stage F K n).graph (stage F K m).graph S e he D h r
  have hImage := selectedGrowthBatchMapSubtype_bValue_image
    F K (stage F K n).graph (stage F K m).graph
    S e he D h r
  calc
    birthBValue F K
      (⟨m, ⟨target,
        selectedGrowthOrdinalIsoSubtype F K
          (stage F K n).graph (stage F K m).graph
          S e he D h r i⟩⟩ : Vertex F K) =
      (taggedSupport (stage F K m).graph
          (GrowthAllowedLocal F) (fun P => K P.card) target ∪
        taggedBlock (stage F K m).graph
          (GrowthAllowedLocal F) (fun P => K P.card) target).image
            (toVertex F K (m + 1)) := by
          rw [birthBValue_of_fresh]
          simp only [birthSupport, birthBlock, Finset.image_union]
    _ = ((selectedBlockBValue (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
          S D r (h.supports r.val r.property)).image
          (selectedGrowthBatchMapSubtype F K
            (stage F K n).graph (stage F K m).graph
            S e he D h)).image
            (toVertex F K (m + 1)) := by
          rw [hImage]
    _ = _ := by
      rw [Finset.image_image]
      rfl

end CFCoherentTower
end BigHrushovski
