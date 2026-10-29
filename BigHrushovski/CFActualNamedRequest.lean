import BigHrushovski.CFCompleteLocalCodeTransport
import BigHrushovski.CFNamedBaseTransport
import BigHrushovski.CFBatchGrowthMembership

/-!
# Construct the actual target request for a named C_F local extension

A finite level lift is defined only on the selected closed old source
S. Given a source request r with support P ⊆ S and an old map f
strictly increasing on S, its literal target support is Q=f[P].
Assume that the old map is induced on P and that Q is strictly
d-closed in the target old stage.

The entire ordered local graph of r can be relabelled along the
canonical order isomorphism P ≃o Q, fixing each fresh Fin ordinal.
This preserves the growth-class predicate, minimal strict d-closedness,
the exact canonical old support and all old-old, old-fresh and
fresh-fresh edges and nonedges.

The target bound is automatic: |Q|=|P| and the original bounded
request already satisfies the same size bound K(|P|). Thus there is
an *actual* target StageRequest, not merely an abstract isomorphic
local extension. This is a finite request construction, not yet the
simultaneous assembly of all source blocks at one target level.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P Q : Type*}
variable [Fintype P] [DecidableEq P]
variable [Fintype Q] [DecidableEq Q]

/-- Transport an already ordered growth-class local type along
an induced isomorphism of its literal old support. The fresh Fin
indices are kept fixed, so no second ordered normalization is
necessary. -/
noncomputable def namedBaseGrowthOrderedLocalType
    (F : ℕ → ℝ)
    (baseP : GraphOn P) (baseQ : GraphOn Q)
    (e : P ≃ Q)
    (hBase : ∀ p q : P,
      baseP.adj p q ↔ baseQ.adj (e p) (e q))
    (n : ℕ)
    (t : OrderedLocalType P baseP
      (fun _ G => G.IsGrowthSparse F Finset.univ) n) :
    OrderedLocalType Q baseQ
      (fun _ G => G.IsGrowthSparse F Finset.univ) n :=
  { graph := namedBaseGraph e t.graph
    base_agrees := fun q r =>
      namedBase_old_adj_iff e t.graph baseP baseQ
        t.base_agrees hBase q r
    allowed := (namedBase_growthSparse_iff F e t.graph).mpr t.allowed
    minimal := (namedBase_minimal_iff e t.graph).mpr t.minimal
    exact_support :=
      (namedBase_exactSupport_iff e t.graph).mpr t.exact_support }

/-- The relabelled ordered local type has exactly the
named-base pullback graph, without a fresh-ordinal permutation. -/
theorem namedBaseGrowthOrderedLocalType_graph
    (F : ℕ → ℝ)
    (baseP : GraphOn P) (baseQ : GraphOn Q)
    (e : P ≃ Q)
    (hBase : ∀ p q : P,
      baseP.adj p q ↔ baseQ.adj (e p) (e q))
    (n : ℕ)
    (t : OrderedLocalType P baseP
      (fun _ G => G.IsGrowthSparse F Finset.univ) n) :
    (namedBaseGrowthOrderedLocalType F baseP baseQ
      e hBase n t).graph = namedBaseGraph e t.graph := rfl

end CFLocalCatalogue

namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- The canonical order isomorphism on the literal support
agrees pointwise with the prescribed old-source map. -/
theorem supportOrderIsoOn_val
    (S P : Finset U) (f : U → V)
    (hf : StrictMonoOn f S) (hP : P ⊆ S)
    (Q : Finset V) (hQ : Q = P.image f)
    (p : SupportCarrier U P) :
    (supportOrderIsoOn S P f hf hP Q hQ p).val = f p.val := by
  rfl

/-- The source and literal target supports have the same
cardinality. No global injectivity assumption on f is needed. -/
theorem supportOrderIsoOn_card
    (S P : Finset U) (f : U → V)
    (hf : StrictMonoOn f S) (hP : P ⊆ S)
    (Q : Finset V) (hQ : Q = P.image f) :
    P.card = Q.card := by
  classical
  let e := supportOrderIsoOn S P f hf hP Q hQ
  have h := Fintype.card_congr e.toEquiv
  simpa only [Fintype.card_coe] using h

/-- Construct the actual target request over the literal named
support Q=f[P]. The source request's bound automatically applies
to Q because |Q|=|P|. The target support's strict d-closedness
is the sole ambient predimension input. -/
noncomputable def transportGrowthStageRequest
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
    StageRequest H (GrowthAllowedLocal F)
      (fun Q => K Q.card) := by
  classical
  let Q : Finset V := r.support.image f
  let e : SupportCarrier U r.support ≃o SupportCarrier V Q :=
    supportOrderIsoOn S r.support f hf hSub Q rfl
  let baseP := supportGraph G r.support
  let baseQ := supportGraph H Q
  have hBase' : ∀ p q : SupportCarrier U r.support,
      baseP.adj p q ↔ baseQ.adj (e p) (e q) := by
    intro p q
    change G.adj p.val q.val ↔
      H.adj (e p).val (e q).val
    simpa only [supportOrderIsoOn_val] using hBase p q
  let local : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier V Q) baseQ
      (GrowthAllowedLocal F Q) r.code.1.val :=
    CFLocalCatalogue.namedBaseGrowthOrderedLocalType
      F baseP baseQ e.toEquiv hBase' r.code.1.val r.code.2
  have hCard : r.support.card = Q.card :=
    supportOrderIsoOn_card S r.support f hf hSub Q rfl
  have hBound : r.code.1.val ≤ K Q.card := by
    rw [← hCard]
    exact Nat.lt_succ_iff.mp r.code.1.isLt
  exact ⟨Q, hClosed,
    CFLocalCatalogue.toBounded baseQ (GrowthAllowedLocal F Q)
      (K Q.card) r.code.1.val hBound local⟩

/-- The constructed request has the literal transported support. -/
theorem transportGrowthStageRequest_support
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
    (transportGrowthStageRequest F K G H S f hf r
      hSub hBase hClosed).support = r.support.image f := rfl

/-- The transported request uses the same fresh size, with
no new numerical assumption on the target bound. -/
theorem transportGrowthStageRequest_size
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
    (transportGrowthStageRequest F K G H S f hf r
      hSub hBase hClosed).code.1.val = r.code.1.val := rfl

end CFStageCatalogue
end BigHrushovski
