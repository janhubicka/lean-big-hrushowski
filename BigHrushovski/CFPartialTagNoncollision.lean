import BigHrushovski.CFActualSubtypeSelectedBatch
import BigHrushovski.CFRequestLexInjection

/-!
# Injectivity of actual C_F request tags under partial old maps

When a prescribed old embedding is defined only on a selected finite
source S, different literal source requests must not collapse to the
same target request. The target may have an empty old carrier and the
complete source old stage need not embed there.

First prove that the literal image of a finite support P⊆S reflects
equality of support sets under any injective e:S→V. Next compare
the complete source request keys: equal target tags have equal target
supports, fresh sizes, and full ordered adjacency matrices. The
already certified partial-source request construction and code
naturality transport these data back to the source. Injectivity of
the complete literal request key then identifies the source tags.

No total map U→V, abstract isomorphism-class quotient, or arbitrary
numbering of request tags is used.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The image of a literal support under an injective map of the
selected old source reflects equality of the original supports.
This works when S or V is empty; the map has domain only S. -/
theorem supportImage_partial_reflects_eq
    (S P Q : Finset U) (hP : P ⊆ S) (hQ : Q ⊆ S)
    (e : SupportCarrier U S → V) (he : Function.Injective e)
    (hImage :
      CFNamedSupport.supportImage S P hP e =
        CFNamedSupport.supportImage S Q hQ e) :
    P = Q := by
  classical
  ext x
  constructor
  · intro hx
    have hxImage :
        e ⟨x, hP hx⟩ ∈ CFNamedSupport.supportImage S P hP e :=
      Finset.mem_image.mpr
        ⟨(⟨x, hx⟩ : SupportCarrier U P),
          Finset.mem_attach P _, rfl⟩
    rw [hImage] at hxImage
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hxImage
    have hSource :
        (⟨x, hP hx⟩ : SupportCarrier U S) =
          ⟨q.val, hQ q.property⟩ := he hq.symm
    have hVal : x = q.val := congrArg Subtype.val hSource
    simpa [hVal] using q.property
  · intro hx
    have hxImage :
        e ⟨x, hQ hx⟩ ∈ CFNamedSupport.supportImage S Q hQ e :=
      Finset.mem_image.mpr
        ⟨(⟨x, hx⟩ : SupportCarrier U Q),
          Finset.mem_attach Q _, rfl⟩
    rw [← hImage] at hxImage
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hxImage
    have hSource :
        (⟨x, hQ hx⟩ : SupportCarrier U S) =
          ⟨p.val, hP p.property⟩ := he hp.symm
    have hVal : x = p.val := congrArg Subtype.val hSource
    simpa [hVal] using p.property

/-- The actual target request retains the source request's fresh
size under the genuinely partial old map. -/
theorem selectedGrowthTagSubtype_size
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    (selectedGrowthTagSubtype F K G H S e he D h r).code.1.val =
      r.val.code.1.val := by
  exact transportGrowthStageRequest_partial_size F K G H S e he
    r.val (h.supports r.val r.property)
    (h.induced r.val r.property (h.supports r.val r.property))
    (h.closed r.val r.property (h.supports r.val r.property))

/-- The actual target request's full ordered adjacency matrix agrees
with the source matrix, not only with its positive edges. -/
theorem selectedGrowthTagSubtype_adjacencyCode
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D)
    (r : SelectedRequests G (GrowthAllowedLocal F)
      (fun P => K P.card) D) :
    requestAdjacencyCode G (GrowthAllowedLocal F)
        (fun P => K P.card) r.val =
      requestAdjacencyCode H (GrowthAllowedLocal F)
        (fun Q => K Q.card)
        (selectedGrowthTagSubtype F K G H S e he D h r) := by
  exact transportGrowthStageRequest_partial_adjacencyCode
    F K G H S e he r.val
    (h.supports r.val r.property)
    (h.induced r.val r.property (h.supports r.val r.property))
    (h.closed r.val r.property (h.supports r.val r.property))

/-- Literal source requests cannot collapse to the same actual
target request under a genuinely partial old embedding. -/
theorem selectedGrowthTagSubtype_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D) :
    Function.Injective (selectedGrowthTagSubtype F K G H S e he D h) := by
  classical
  intro r s hrs
  have hImage :
      CFNamedSupport.supportImage S r.val.support
          (h.supports r.val r.property) e =
        CFNamedSupport.supportImage S s.val.support
          (h.supports s.val s.property) e := by
    calc
      _ = (selectedGrowthTagSubtype F K G H S e he D h r).support :=
        (selectedGrowthTagSubtype_support F K G H S e he D h r).symm
      _ = (selectedGrowthTagSubtype F K G H S e he D h s).support := by
        rw [hrs]
      _ = _ := selectedGrowthTagSubtype_support F K G H S e he D h s
  have hSupport : r.val.support = s.val.support :=
    supportImage_partial_reflects_eq S r.val.support s.val.support
      (h.supports r.val r.property)
      (h.supports s.val s.property)
      e he.injective hImage
  have hSize : r.val.code.1.val = s.val.code.1.val := by
    calc
      _ = (selectedGrowthTagSubtype F K G H S e he D h r).code.1.val :=
        (selectedGrowthTagSubtype_size F K G H S e he D h r).symm
      _ = (selectedGrowthTagSubtype F K G H S e he D h s).code.1.val := by
        rw [hrs]
      _ = _ := selectedGrowthTagSubtype_size F K G H S e he D h s
  have hBits :
      requestAdjacencyCode G (GrowthAllowedLocal F)
          (fun P => K P.card) r.val =
        requestAdjacencyCode G (GrowthAllowedLocal F)
          (fun P => K P.card) s.val := by
    calc
      _ = requestAdjacencyCode H (GrowthAllowedLocal F)
          (fun Q => K Q.card)
          (selectedGrowthTagSubtype F K G H S e he D h r) :=
        selectedGrowthTagSubtype_adjacencyCode F K G H S e he D h r
      _ = requestAdjacencyCode H (GrowthAllowedLocal F)
          (fun Q => K Q.card)
          (selectedGrowthTagSubtype F K G H S e he D h s) := by
        rw [hrs]
      _ = _ :=
        (selectedGrowthTagSubtype_adjacencyCode F K G H S e he D h s).symm
  apply Subtype.ext
  apply requestLexKey_injective G (GrowthAllowedLocal F)
    (fun P => K P.card)
  change
    (requestSupportTuple G (GrowthAllowedLocal F)
      (fun P => K P.card) r.val,
      (r.val.code.1.val, requestAdjacencyCode G
        (GrowthAllowedLocal F) (fun P => K P.card) r.val)) =
    (requestSupportTuple G (GrowthAllowedLocal F)
      (fun P => K P.card) s.val,
      (s.val.code.1.val, requestAdjacencyCode G
        (GrowthAllowedLocal F) (fun P => K P.card) s.val))
  apply Prod.ext
  · change r.val.support.sort (· ≤ ·) =
      s.val.support.sort (· ≤ ·)
    rw [hSupport]
  · exact Prod.ext hSize hBits

/-- The entire actual partial-source simultaneous map is injective.
The old map is injective by strict monotonicity, request tags do
not collide by the complete-code lemma, and every fresh Fin cast
is a bijection. -/
theorem selectedGrowthBatchMapSubtype_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (e : SupportCarrier U S → V)
    (he : StrictMono e)
    (D : Finset (Requests G (GrowthAllowedLocal F)
      (fun P => K P.card)))
    (h : SelectedGrowthTransportSubtype F K G H S e D) :
    Function.Injective (selectedGrowthBatchMapSubtype F K G H S e he D h) := by
  exact selectedTargetMapSubtype_injective
    G (GrowthAllowedLocal F) (fun P => K P.card)
    H (GrowthAllowedLocal F) (fun Q => K Q.card)
    S D e he.injective
    (selectedGrowthTagSubtype F K G H S e he D h)
    (selectedGrowthTagSubtype_injective F K G H S e he D h)
    (fun r i => selectedGrowthOrdinalIsoSubtype F K G H S e he D h r i)
    (fun r => (selectedGrowthOrdinalIsoSubtype F K G H S e he D h r).injective)

end CFStageCatalogue
end BigHrushovski
