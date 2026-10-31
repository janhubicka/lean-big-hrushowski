import BigHrushovski.CFActualSubtypeStageOrder
import BigHrushovski.CFActualSubtypeBatchInduced
import BigHrushovski.CFSelectedSubtypeBValues

/-!
# The complete functional map at one C_F represented level

The old source is a genuine selected subtype S of the complete old
stage U; there is no requirement to extend its embedding to U.

For a new selected vertex, the complete auxiliary b-value is its
literal old support together with the WHOLE new request block.
For an old vertex, the b-value is already contained in the selected
old source, and its preservation is the induction hypothesis.
We assemble these two cases into a single all-vertices equality,
without reintroducing a total old-stage map.

This is the missing one-level functional-value interface; the
induction through represented levels and uniqueness remain separate.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Complete b-values on the selected one-level source.
Old b-values are already on the selected old subtype, while new
b-values contain the whole old support plus the complete new block. -/
noncomputable def selectedOneLevelBValue
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (S : Finset U) (D : Finset (Requests G Allowed bound))
    (hSupports : ∀ r : SelectedRequests G Allowed bound D,
      r.val.support ⊆ S)
    (oldB : SupportCarrier U S → Finset (SupportCarrier U S)) :
    SelectedCarrier G Allowed bound S D →
      Finset (SelectedCarrier G Allowed bound S D)
  | Sum.inl u =>
      (oldB u).image (fun w =>
        (Sum.inl w : SelectedCarrier G Allowed bound S D))
  | Sum.inr ⟨r, _⟩ =>
      selectedBlockBValue G Allowed bound S D r (hSupports r)

/-- Complete b-values on the full target tagged successor level.
Old values retain their prior stage values; fresh values have their
literal named support and whole tagged fresh block. -/
noncomputable def targetOneLevelBValue
    (H : GraphOn V) (AllowedV : AllowedLocal V)
    (boundV : Finset V → ℕ)
    (oldB : V → Finset V) :
    LevelCarrier H AllowedV boundV →
      Finset (LevelCarrier H AllowedV boundV)
  | Sum.inl v =>
      (oldB v).image (fun w =>
        (Sum.inl w : LevelCarrier H AllowedV boundV))
  | Sum.inr ⟨r, _⟩ =>
      taggedSupport H AllowedV boundV r ∪
        taggedBlock H AllowedV boundV r

/-- A simultaneous partial-source map preserves every complete
one-level b-value, assuming the old b-values are transported by the
given old embedding. This is stronger than the new-block-only lemma. -/
theorem selectedGrowthBatchMapSubtype_allBValues
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (oldB : SupportCarrier U S → Finset (SupportCarrier U S))
    (targetOldB : V → Finset V)
    (hOldB : ∀ u : SupportCarrier U S,
      (oldB u).image e = targetOldB (e u))
    (x : SelectedCarrier G (GrowthAllowedLocal F)
      (fun P => K P.card) S D) :
    (selectedOneLevelBValue G (GrowthAllowedLocal F)
      (fun P => K P.card) S D
      (fun r => h.supports r.val r.property) oldB x).image
        (selectedGrowthBatchMapSubtype F K G H S e he D h) =
    targetOneLevelBValue H (GrowthAllowedLocal F)
      (fun P => K P.card) targetOldB
      (selectedGrowthBatchMapSubtype F K G H S e he D h x) := by
  classical
  cases x with
  | inl u =>
      change
        ((oldB u).image
          (fun w : SupportCarrier U S =>
            (Sum.inl w : SelectedCarrier G (GrowthAllowedLocal F)
              (fun P => K P.card) S D))).image
              (selectedGrowthBatchMapSubtype F K G H S e he D h) =
        (targetOldB (e u)).image
          (fun v : V => (Sum.inl v :
            LevelCarrier H (GrowthAllowedLocal F) (fun P => K P.card)))
      rw [Finset.image_image]
      change (oldB u).image
        (fun w : SupportCarrier U S =>
          (Sum.inl (e w) :
            LevelCarrier H (GrowthAllowedLocal F) (fun P => K P.card))) =
        (targetOldB (e u)).image
          (fun v : V => (Sum.inl v :
            LevelCarrier H (GrowthAllowedLocal F) (fun P => K P.card)))
      calc
        _ = ((oldB u).image e).image
            (fun v : V => (Sum.inl v :
              LevelCarrier H (GrowthAllowedLocal F) (fun P => K P.card))) := by
                rw [Finset.image_image]
        _ = _ := by rw [hOldB u]
  | inr z =>
      rcases z with ⟨r, i⟩
      change
        (selectedBlockBValue G (GrowthAllowedLocal F)
          (fun P => K P.card) S D r
          (h.supports r.val r.property)).image
            (selectedGrowthBatchMapSubtype F K G H S e he D h) =
          taggedSupport H (GrowthAllowedLocal F) (fun P => K P.card)
            (selectedGrowthTagSubtype F K G H S e he D h r) ∪
          taggedBlock H (GrowthAllowedLocal F) (fun P => K P.card)
            (selectedGrowthTagSubtype F K G H S e he D h r)
      exact selectedGrowthBatchMapSubtype_bValue_image
        F K G H S e he D h r

end CFStageCatalogue

namespace CFCoherentTower

open CFStageCatalogue

/-- One complete finite C_F level extension over a genuinely partial
old stage embedding. The map is injective, induced (including
nonedges), order-preserving and order-reflecting for the *inherited*
stage order, has strictly d-closed image, and transports every
complete b-value. The hypotheses on old values are those used
by the induction through represented levels. -/
theorem selectedGrowthBatchMapSubtype_oneLevel
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (S : Finset (stage F K n).carrier)
    (e : SupportCarrier (stage F K n).carrier S →
      (stage F K m).carrier)
    (he : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      letI : LinearOrder (stage F K m).carrier :=
        stageLinearOrder F K m
      StrictMono e)
    (hOldAdj : ∀ u v : SupportCarrier (stage F K n).carrier S,
      (stage F K n).graph.adj u.val v.val ↔
        (stage F K m).graph.adj (e u) (e v))
    (hOldClosed : (stage F K m).graph.toPredimension.IsDClosed
      (selectedOldImage S e) Finset.univ)
    (D : Finset (Requests (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K
      (stage F K n).graph (stage F K m).graph S e D)
    (oldB : SupportCarrier (stage F K n).carrier S →
      Finset (SupportCarrier (stage F K n).carrier S))
    (targetOldB : (stage F K m).carrier →
      Finset (stage F K m).carrier)
    (hOldB : ∀ u : SupportCarrier (stage F K n).carrier S,
      (oldB u).image e = targetOldB (e u)) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K m).carrier :=
      stageLinearOrder F K m
    let T := selectedGrowthBatchMapSubtype F K
      (stage F K n).graph (stage F K m).graph S e he D h
    Function.Injective T ∧
    (∀ x y : SelectedCarrier (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D,
      (stage F K (n + 1)).graph.adj
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card) S D x)
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card) S D y) ↔
      (stage F K (m + 1)).graph.adj (T x) (T y)) ∧
    (∀ x y : SelectedCarrier (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D,
      stageLt F K (n + 1)
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card) S D x)
        (selectedSourceMap (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card) S D y) ↔
      stageLt F K (m + 1) (T x) (T y)) ∧
    (stage F K (m + 1)).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset (SelectedCarrier (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D)).image T)
      Finset.univ ∧
    (∀ x : SelectedCarrier (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D,
      (selectedOneLevelBValue (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) S D
        (fun r => h.supports r.val r.property) oldB x).image T =
      targetOneLevelBValue (stage F K m).graph
        (GrowthAllowedLocal F) (fun P => K P.card)
        targetOldB (T x)) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  refine ⟨selectedGrowthBatchMapSubtype_injective F K
      (stage F K n).graph (stage F K m).graph S e he D h,
    ?_, ?_, ?_, ?_⟩
  · intro x y
    exact selectedGrowthBatchMapSubtype_induced F K
      (stage F K n).graph (stage F K m).graph
      S e he hOldAdj D h x y
  · intro x y
    exact selectedGrowthBatchMapSubtype_stageOrder_iff F K
      n m S e he D h x y
  · exact selectedGrowthBatchMapSubtype_dClosed_full F K
      (stage F K n).graph (stage F K m).graph
      S e he D h hOldClosed
  · intro x
    exact selectedGrowthBatchMapSubtype_allBValues F K
      (stage F K n).graph (stage F K m).graph
      S e he D h oldB targetOldB hOldB x

end CFCoherentTower
end BigHrushovski
