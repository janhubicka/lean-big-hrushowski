import BigHrushovski.CFActualSelectedBatchMap
import BigHrushovski.CFLiteralBoundaryTransport

/-!
# Inducedness of the actual simultaneous selected C_F level map

The actual selected map sends all source blocks born at one level
into the *same* target level, with literal target request tags and
canonical fresh ordinal isomorphisms.

We use the complete named-base local graph transport to prove
the two local graph comparisons needed by the previously verified
simultaneous-map inducedness theorem:
- every old-fresh boundary edge and nonedge is reflected, including
  source old vertices outside a block's support;
- every fresh-fresh edge and nonedge within a block is reflected.

Cross-block nonedges are supplied by the actual tagged batch graph.
The old-old graph comparison is the explicit hypothesis that the
already embedded old source is induced.

No level-order or complete b-value preservation is asserted yet.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Source and target fresh-fresh adjacency agree for each selected
literal request, because the transported local graph fixes every
fresh Fin ordinal and preserves all fresh-fresh nonedges. -/
theorem selectedGrowthLocal_fresh_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (i j : Fin r.val.code.1.val) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨r.val, j⟩) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (Sum.inr ⟨selectedGrowthTag F K G H S f hf D h r,
        selectedGrowthOrdinalIso F K G H S f hf D h r i⟩)
      (Sum.inr ⟨selectedGrowthTag F K G H S f hf D h r,
        selectedGrowthOrdinalIso F K G H S f hf D h r j⟩) := by
  let t := selectedGrowthTag F K G H S f hf D h r
  let e := supportOrderIsoOn S r.val.support f hf
    (h.supports r.val r.property) (r.val.support.image f) rfl
  have hSource := levelGraph_local_adj_iff
    G (GrowthAllowedLocal F) (fun P => K P.card)
    r.val (Sum.inr i) (Sum.inr j)
  have hTarget := levelGraph_local_adj_iff
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    t (Sum.inr (selectedGrowthOrdinalIso F K G H S f hf D h r i))
      (Sum.inr (selectedGrowthOrdinalIso F K G H S f hf D h r j))
  calc
    _ ↔ r.val.code.2.graph.adj (Sum.inr i) (Sum.inr j) := hSource
    _ ↔ t.code.2.graph.adj
        (Sum.inr (selectedGrowthOrdinalIso F K G H S f hf D h r i))
        (Sum.inr (selectedGrowthOrdinalIso F K G H S f hf D h r j)) := by
          change r.val.code.2.graph.adj (Sum.inr i) (Sum.inr j) ↔
            (CFLocalCatalogue.namedBaseGraph e.toEquiv
              r.val.code.2.graph).adj (Sum.inr i) (Sum.inr j)
          exact (CFLocalCatalogue.namedBaseGraph_fresh_iff
            r.val.support (r.val.support.image f)
            e.toEquiv r.val.code.1.val r.val.code.2.graph i j).symm
    _ ↔ _ := hTarget.symm

/-- Every old-fresh boundary is transported exactly, including
nonedges to selected old vertices outside the source support.
Injectivity on S is essential in the reverse direction. -/
theorem selectedGrowthLocal_boundary_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (hfInj : Set.InjOn f S)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (u : SupportCarrier U S)
    (i : Fin r.val.code.1.val) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (Sum.inl u.val) (Sum.inr ⟨r.val, i⟩) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (Sum.inl (f u.val))
      (Sum.inr ⟨selectedGrowthTag F K G H S f hf D h r,
        selectedGrowthOrdinalIso F K G H S f hf D h r i⟩) := by
  let t := selectedGrowthTag F K G H S f hf D h r
  let e := supportOrderIsoOn S r.val.support f hf
    (h.supports r.val r.property) (r.val.support.image f) rfl
  have hVal : ∀ p : SupportCarrier U r.val.support,
      (e p).val = f p.val := by
    intro p
    exact supportOrderIsoOn_val S r.val.support f hf
      (h.supports r.val r.property) (r.val.support.image f) rfl p
  have hBoundary := CFLocalCatalogue.namedBaseGraph_full_boundary_iff
    r.val.support (r.val.support.image f)
    S (h.supports r.val r.property) f hfInj e.toEquiv
    hVal r.val.code.1.val r.val.code.2.graph u.val u.property i
  have hSource := tagged_old_fresh_adj_iff
    G (GrowthAllowedLocal F) (fun P => K P.card) r.val u.val i
  have hTarget := tagged_old_fresh_adj_iff
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    t (f u.val) (selectedGrowthOrdinalIso F K G H S f hf D h r i)
  calc
    _ ↔ (∃ p : SupportCarrier U r.val.support,
      p.val = u.val ∧
        r.val.code.2.graph.adj (Sum.inl p) (Sum.inr i)) := hSource
    _ ↔ (∃ q : SupportCarrier V (r.val.support.image f),
      q.val = f u.val ∧
        (CFLocalCatalogue.namedBaseGraph e.toEquiv
          r.val.code.2.graph).adj (Sum.inl q) (Sum.inr i)) := hBoundary
    _ ↔ _ := hTarget.symm

/-- The actual entire selected batch map is an induced graph
embedding into the target simultaneous level: old-old,
old-fresh and same-block fresh-fresh comparisons are all
derived from the literal constructed local graphs, while
cross-block nonedges follow from noncollision of tags. -/
theorem selectedGrowthBatchMap_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (hOld : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (f u.val) (f v.val))
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransport F K G H S f D)
    (x y : SelectedCarrier G (GrowthAllowedLocal F)
      (fun P => K P.card) S D) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (selectedSourceMap G (GrowthAllowedLocal F) (fun P => K P.card)
        S D x)
      (selectedSourceMap G (GrowthAllowedLocal F) (fun P => K P.card)
        S D y) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (selectedGrowthBatchMap F K G H S f hf D h x)
      (selectedGrowthBatchMap F K G H S f hf D h y) := by
  have hfInj : Set.InjOn f S := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((ne_of_lt (hf ha hb hlt)) hab)
    · exact heq
    · exact False.elim ((ne_of_lt (hf hb ha hgt)) hab.symm)
  exact selectedTargetMap_induced
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D f hOld
    (selectedGrowthTag F K G H S f hf D h)
    (selectedGrowthTag_injective F K G H S f hf D h)
    (fun r i => selectedGrowthOrdinalIso F K G H S f hf D h r i)
    (selectedGrowthLocal_boundary_iff F K G H S f hf D h hfInj)
    (selectedGrowthLocal_fresh_iff F K G H S f hf D h)
    x y

end CFStageCatalogue
end BigHrushovski
