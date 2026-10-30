import BigHrushovski.CFPartialBoundaryTransport
import BigHrushovski.CFPartialTagNoncollision
import BigHrushovski.CFSelectedSubtypeInduced

/-!
# Inducedness of the actual selected C_F batch with partial old domain

A genuine old-source embedding e:S→V is not necessarily extendible
to the whole old stage U. For every selected source request, the
actual target request is obtained by the named-support construction
of CFPartialOldSourceRequest, fixing each fresh Fin ordinal.

We now discharge both local graph hypotheses of the generic
partial simultaneous-map inducedness theorem:
* every selected old-to-fresh edge and nonedge is preserved and
  reflected, including selected old vertices outside a block's
  literal named support;
* all internal fresh-to-fresh edges and nonedges are preserved
  and reflected by the named-base pullback graph.

The actual target tags are injective by complete code noncollision,
so all cross-block nonedges are reflected. The resulting single
simultaneous map is induced on the entire selected old+fresh
carrier, including for the empty-target old stage.

Its exact inherited order and complete b-values, and the induction
through represented levels, are separate proof obligations.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Exact fresh-fresh edge and nonedge transport for the actual
partial-domain named-support request. No change to fresh ordinals
is made by the transported local graph. -/
theorem selectedGrowthLocalSubtype_fresh_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (i j : Fin r.val.code.1.val) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (Sum.inr ⟨r.val, i⟩) (Sum.inr ⟨r.val, j⟩) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (Sum.inr ⟨selectedGrowthTagSubtype F K G H S e he D h r,
        selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i⟩)
      (Sum.inr ⟨selectedGrowthTagSubtype F K G H S e he D h r,
        selectedGrowthOrdinalIsoSubtype F K G H S e he D h r j⟩) := by
  let t := selectedGrowthTagSubtype F K G H S e he D h r
  let iso := partialSupportOrderIso S r.val.support
    (h.supports r.val r.property) e he
  have hSource := levelGraph_local_adj_iff
    G (GrowthAllowedLocal F) (fun P => K P.card)
    r.val (Sum.inr i) (Sum.inr j)
  have hTarget := levelGraph_local_adj_iff
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    t
    (Sum.inr (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i))
    (Sum.inr (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r j))
  calc
    _ ↔ r.val.code.2.graph.adj (Sum.inr i) (Sum.inr j) := hSource
    _ ↔ t.code.2.graph.adj
        (Sum.inr (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i))
        (Sum.inr (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r j)) := by
          change r.val.code.2.graph.adj (Sum.inr i) (Sum.inr j) ↔
            (CFLocalCatalogue.namedBaseGraph iso.toEquiv
              r.val.code.2.graph).adj (Sum.inr i) (Sum.inr j)
          exact (CFLocalCatalogue.namedBaseGraph_fresh_iff
            r.val.support
            (CFNamedSupport.supportImage S r.val.support
              (h.supports r.val r.property) e)
            iso.toEquiv r.val.code.1.val r.val.code.2.graph i j).symm
    _ ↔ _ := hTarget.symm

/-- Exact old-to-fresh boundary of the actual partial target request,
including reflection of absent edges to old vertices outside the
complete source support. -/
theorem selectedGrowthLocalSubtype_boundary_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D)
    (u : SupportCarrier U S)
    (i : Fin r.val.code.1.val) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (Sum.inl u.val) (Sum.inr ⟨r.val, i⟩) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (Sum.inl (e u))
      (Sum.inr ⟨selectedGrowthTagSubtype F K G H S e he D h r,
        selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i⟩) := by
  let t := selectedGrowthTagSubtype F K G H S e he D h r
  let iso := partialSupportOrderIso S r.val.support
    (h.supports r.val r.property) e he
  have hVal : ∀ p : SupportCarrier U r.val.support,
      (iso p).val =
        e ⟨p.val, (h.supports r.val r.property) p.property⟩ := by
    intro p
    exact partialSupportOrderIso_val S r.val.support
      (h.supports r.val r.property) e he p
  have hBoundary := CFLocalCatalogue.namedBaseGraph_partial_boundary_iff
    S r.val.support (h.supports r.val r.property)
    e he.injective
    (CFNamedSupport.supportImage S r.val.support
      (h.supports r.val r.property) e)
    iso.toEquiv hVal
    r.val.code.1.val r.val.code.2.graph u i
  have hSource := tagged_old_fresh_adj_iff
    G (GrowthAllowedLocal F) (fun P => K P.card)
    r.val u.val i
  have hTarget := tagged_old_fresh_adj_iff
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    t (e u)
    (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)
  calc
    _ ↔ (∃ p : SupportCarrier U r.val.support,
      p.val = u.val ∧
        r.val.code.2.graph.adj (Sum.inl p) (Sum.inr i)) := hSource
    _ ↔ (∃ q : SupportCarrier V
        (CFNamedSupport.supportImage S r.val.support
          (h.supports r.val r.property) e),
      q.val = e u ∧
        (CFLocalCatalogue.namedBaseGraph iso.toEquiv
          r.val.code.2.graph).adj (Sum.inl q) (Sum.inr i)) := hBoundary
    _ ↔ _ := hTarget.symm

/-- The actual simultaneous selected-batch map built from a genuinely
partial old map is induced on all selected vertices: all edges and
nonedges are transported, including between different blocks. -/
theorem selectedGrowthBatchMapSubtype_induced
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (hOld : ∀ u v : SupportCarrier U S,
      G.adj u.val v.val ↔ H.adj (e u) (e v))
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (x y : SelectedCarrier G (GrowthAllowedLocal F)
      (fun P => K P.card) S D) :
    (levelGraph G (GrowthAllowedLocal F) (fun P => K P.card)).adj
      (selectedSourceMap G (GrowthAllowedLocal F)
        (fun P => K P.card) S D x)
      (selectedSourceMap G (GrowthAllowedLocal F)
        (fun P => K P.card) S D y) ↔
    (levelGraph H (GrowthAllowedLocal F) (fun Q => K Q.card)).adj
      (selectedGrowthBatchMapSubtype F K G H S e he D h x)
      (selectedGrowthBatchMapSubtype F K G H S e he D h y) := by
  exact selectedTargetMapSubtype_induced
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e hOld
    (selectedGrowthTagSubtype F K G H S e he D h)
    (selectedGrowthTagSubtype_injective F K G H S e he D h)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)
    (fun u r i => selectedGrowthLocalSubtype_boundary_iff
      F K G H S e he D h r u i)
    (selectedGrowthLocalSubtype_fresh_iff F K G H S e he D h)
    x y

end CFStageCatalogue
end BigHrushovski
