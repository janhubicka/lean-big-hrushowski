import BigHrushovski.CFActualSelectedBatchInduced

/-!
# Exact C_F request order of the simultaneous selected batch map

A finite tagged level orders all old vertices first, and compares
fresh vertices by the increasing old support tuple, fresh-block
size, complete ordered adjacency matrix and internal fresh ordinal.
The same exact comparison has already been verified as the
canonical numerical request rank in the actual C_F stage tower.

Here we express the strict comparison directly in these keys and
prove that the *actual* simultaneous selected-batch map preserves
and reflects it, without choosing an arbitrary enumeration of
request tags. The old map needs to be increasing only on the
selected source S. For two fresh blocks, the constructed target
request map preserves the exact lexicographic request comparison
and the canonical finite ordinal maps preserve each ordinal value.

The next step will explicitly identify this comparison with the
inherited linear order on the actual finite stage carriers, using
the already verified stage-order decomposition lemmas.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The precise manuscript comparison at one tagged finite level:
old vertices retain their old order and precede every fresh vertex;
fresh blocks are compared by complete request codes, then by their
internal natural ordinal. -/
def TaggedLexLt
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    LevelCarrier G Allowed bound →
      LevelCarrier G Allowed bound → Prop
  | Sum.inl u, Sum.inl v => u < v
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => False
  | Sum.inr ⟨r, i⟩, Sum.inr ⟨s, j⟩ =>
      RequestLexLt G Allowed bound r s ∨
        (r = s ∧ i.val < j.val)

/-- The actual simultaneous C_F map preserves and reflects
the exact one-level lexicographic request order, including
proper-prefix support comparisons and every internal ordinal.
Only the selected old vertices need to be increasing. -/
theorem selectedGrowthBatchMap_taggedLex_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (x y : SelectedCarrier G (GrowthAllowedLocal F)
      (fun P => K P.card) S D) :
    TaggedLexLt G (GrowthAllowedLocal F) (fun P => K P.card)
      (selectedSourceMap G (GrowthAllowedLocal F)
        (fun P => K P.card) S D x)
      (selectedSourceMap G (GrowthAllowedLocal F)
        (fun P => K P.card) S D y) ↔
    TaggedLexLt H (GrowthAllowedLocal F) (fun Q => K Q.card)
      (selectedGrowthBatchMap F K G H S f hf D h x)
      (selectedGrowthBatchMap F K G H S f hf D h y) := by
  cases x with
  | inl u =>
      cases y with
      | inl v =>
          change u.val < v.val ↔ f u.val < f v.val
          constructor
          · exact hf u.property v.property
          · intro hlt
            rcases lt_trichotomy u.val v.val with h | h | h
            · exact h
            · rw [← h] at hlt
              exact False.elim (lt_irrefl _ hlt)
            · exact False.elim
                (lt_asymm (hf v.property u.property h) hlt)
      | inr z =>
          exact Iff.rfl
  | inr x =>
      cases y with
      | inl v =>
          exact Iff.rfl
      | inr y =>
          rcases x with ⟨r, i⟩
          rcases y with ⟨s, j⟩
          change
            (RequestLexLt G (GrowthAllowedLocal F)
                (fun P => K P.card) r.val s.val ∨
              (r.val = s.val ∧ i.val < j.val)) ↔
            (RequestLexLt H (GrowthAllowedLocal F)
                (fun Q => K Q.card)
                (selectedGrowthTag F K G H S f hf D h r)
                (selectedGrowthTag F K G H S f hf D h s) ∨
              (selectedGrowthTag F K G H S f hf D h r =
                  selectedGrowthTag F K G H S f hf D h s ∧
                (selectedGrowthOrdinalIso F K G H S f hf D h r i).val <
                  (selectedGrowthOrdinalIso F K G H S f hf D h s j).val))
          have hReq := transportGrowthStageRequest_order_iff
            F K G H S f hf r.val s.val
            (h.supports r.val r.property)
            (h.supports s.val s.property)
            (h.induced r.val r.property)
            (h.induced s.val s.property)
            (h.closed r.val r.property)
            (h.closed s.val s.property)
          have hTag :
              (r.val = s.val) ↔
                (selectedGrowthTag F K G H S f hf D h r =
                  selectedGrowthTag F K G H S f hf D h s) := by
            constructor
            · intro hrs
              have hEq : r = s := Subtype.ext hrs
              rw [hEq]
            · intro hts
              exact congrArg Subtype.val
                ((selectedGrowthTag_injective F K G H S f hf D h) hts)
          have hOrd :
              (i.val < j.val) ↔
                ((selectedGrowthOrdinalIso F K G H S f hf D h r i).val <
                  (selectedGrowthOrdinalIso F K G H S f hf D h s j).val) := by
            rw [selectedGrowthOrdinalIso_val,
              selectedGrowthOrdinalIso_val]
          exact or_congr hReq (and_congr hTag hOrd)

end CFStageCatalogue
end BigHrushovski
