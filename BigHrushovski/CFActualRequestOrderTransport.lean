import BigHrushovski.CFConstructedRequestCode

/-!
# Exact transport of actual C_F requests over a selected old source

The target request is now constructed, not merely postulated.
The named support is its literal image, the fresh size is unchanged,
and the complete ordered adjacency matrix agrees by the
named-base pullback theorem.

Consequently the already verified conditional request-key
transport theorems apply directly: the prescribed old embedding
preserves and reflects the exact lexicographic request order,
distinct source requests have distinct target requests, and
the target request with a given complete transported code is unique.

Only strict monotonicity on the selected old source is assumed.
The support images must be d-closed in the target old stage.
The simultaneous same-level block map is still to be assembled.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The actual constructed target request has the complete
transport certificate. In particular, adjacency-code equality
is proved, not supplied as an additional assumption. -/
theorem transportGrowthStageRequest_codeTransportOn
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hClosed : H.toPredimension.IsDClosed
      (r.support.image f) Finset.univ) :
    RequestCodeTransportOn G H
      (GrowthAllowedLocal F) (GrowthAllowedLocal F)
      (fun P => K P.card) (fun Q => K Q.card)
      S f r
      (transportGrowthStageRequest F K G H S f hf
        r hSub hBase hClosed) := by
  exact requestCodeTransportOn_of_namedImage
    G H (GrowthAllowedLocal F) (GrowthAllowedLocal F)
    (fun P => K P.card) (fun Q => K Q.card)
    S f hf r
    (transportGrowthStageRequest F K G H S f hf
      r hSub hBase hClosed)
    hSub
    (transportGrowthStageRequest_support F K G H S f hf
      r hSub hBase hClosed)
    (transportGrowthStageRequest_size F K G H S f hf
      r hSub hBase hClosed)
    (transportGrowthStageRequest_adjacencyCode F K G H S f hf
      r hSub hBase hClosed).symm

/-- The constructed target request is the unique request with
the prescribed complete transported code. -/
theorem transportGrowthStageRequest_unique
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hClosed : H.toPredimension.IsDClosed
      (r.support.image f) Finset.univ)
    (t : StageRequest H (GrowthAllowedLocal F)
      (fun Q => K Q.card))
    (ht : RequestCodeTransportOn G H
      (GrowthAllowedLocal F) (GrowthAllowedLocal F)
      (fun P => K P.card) (fun Q => K Q.card)
      S f r t) :
    t = transportGrowthStageRequest F K G H S f hf
      r hSub hBase hClosed := by
  exact requestCodeTransportOn_unique
    G H (GrowthAllowedLocal F) (GrowthAllowedLocal F)
    (fun P => K P.card) (fun Q => K Q.card)
    S f r t
    (transportGrowthStageRequest F K G H S f hf
      r hSub hBase hClosed)
    ht (transportGrowthStageRequest_codeTransportOn F K G H
      S f hf r hSub hBase hClosed)

/-- Exact comparison of two *constructed* target requests is
equivalent to the source comparison. This includes proper-prefix
support tuples and the complete ordered local graph codes. -/
theorem transportGrowthStageRequest_order_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r s : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hrSub : r.support ⊆ S)
    (hsSub : s.support ⊆ S)
    (hrBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hsBase : ∀ p q : SupportCarrier U s.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hrClosed : H.toPredimension.IsDClosed
      (r.support.image f) Finset.univ)
    (hsClosed : H.toPredimension.IsDClosed
      (s.support.image f) Finset.univ) :
    RequestLexLt G (GrowthAllowedLocal F)
      (fun P => K P.card) r s ↔
    RequestLexLt H (GrowthAllowedLocal F)
      (fun Q => K Q.card)
      (transportGrowthStageRequest F K G H S f hf
        r hrSub hrBase hrClosed)
      (transportGrowthStageRequest F K G H S f hf
        s hsSub hsBase hsClosed) := by
  exact requestLexLt_transportOn_iff
    G H (GrowthAllowedLocal F) (GrowthAllowedLocal F)
    (fun P => K P.card) (fun Q => K Q.card)
    S f hf r s
    (transportGrowthStageRequest F K G H S f hf
      r hrSub hrBase hrClosed)
    (transportGrowthStageRequest F K G H S f hf
      s hsSub hsBase hsClosed)
    (transportGrowthStageRequest_codeTransportOn F K G H
      S f hf r hrSub hrBase hrClosed)
    (transportGrowthStageRequest_codeTransportOn F K G H
      S f hf s hsSub hsBase hsClosed)

/-- Two different source requests cannot be sent to the same
target request by the constructed named-support transport.
No global old-stage injection is assumed. -/
theorem transportGrowthStageRequest_reflects_eq
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U) (f : U → V)
    (hf : StrictMonoOn f S)
    (r s : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hrSub : r.support ⊆ S)
    (hsSub : s.support ⊆ S)
    (hrBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hsBase : ∀ p q : SupportCarrier U s.support,
      G.adj p.val q.val ↔ H.adj (f p.val) (f q.val))
    (hrClosed : H.toPredimension.IsDClosed
      (r.support.image f) Finset.univ)
    (hsClosed : H.toPredimension.IsDClosed
      (s.support.image f) Finset.univ)
    (hEq :
      transportGrowthStageRequest F K G H S f hf
        r hrSub hrBase hrClosed =
      transportGrowthStageRequest F K G H S f hf
        s hsSub hsBase hsClosed) :
    r = s := by
  exact requestCodeTransportOn_reflects_eq
    G H (GrowthAllowedLocal F) (GrowthAllowedLocal F)
    (fun P => K P.card) (fun Q => K Q.card)
    S f hf r s
    (transportGrowthStageRequest F K G H S f hf
      r hrSub hrBase hrClosed)
    (transportGrowthStageRequest F K G H S f hf
      s hsSub hsBase hsClosed)
    (transportGrowthStageRequest_codeTransportOn F K G H
      S f hf r hrSub hrBase hrClosed)
    (transportGrowthStageRequest_codeTransportOn F K G H
      S f hf s hsSub hsBase hsClosed)
    hEq

end CFStageCatalogue
end BigHrushovski
