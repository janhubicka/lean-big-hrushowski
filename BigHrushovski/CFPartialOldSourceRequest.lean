import BigHrushovski.CFActualNamedRequest
import BigHrushovski.CFNamedSupportEquiv

/-!
# Named C_F requests transported by a genuinely partial old map

In finite unique level lifting, the map on old vertices has domain
only the selected finite closed source S, not the whole old stage U.
A total function U → V need not exist: in the first represented
level, S and the target old stage V may both be empty while U is
nonempty. The earlier total-map request transport therefore cannot
be used without a separate empty-target case.

Here we transport a request along the *actual* map
  e : {u : U // u ∈ S} → V.
The source support P is contained in S. We retain its literal
image Q = e[P], with the unique increasing order isomorphism
between the support subtypes. In particular, this construction
also works when S=∅ and V=∅, without choosing an arbitrary
value of V.

The induced old graph and strict d-closedness of Q in the target
old stage remain explicit hypotheses. The local growth predicate,
minimal d-closed step, exact support, and complete fresh ordinal
order are preserved by the previously certified named-base
relabelling. The bound K(|P|) is unchanged because |Q|=|P|.

This constructs an actual target request, but does not yet
identify the complete adjacency matrix or simultaneously attach
the selected blocks.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U V : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]
variable [Fintype V] [LinearOrder V] [DecidableEq V]

/-- Order isomorphism between a literal support P⊆S and its image
under a map defined ONLY on S. No extension of the map U→V is
necessary, including when the target old stage V is empty. -/
noncomputable def partialSupportOrderIso
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V) (he : StrictMono e) :
    SupportCarrier U P ≃o
      SupportCarrier V (CFNamedSupport.supportImage S P hP e) := by
  classical
  let f := CFNamedSupport.restrictedSupportMap S P hP e
  have hf : StrictMono f := by
    intro p q hpq
    exact he hpq
  exact OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono f hf)
    (CFNamedSupport.restrictedSupportMap_surjective S P hP e)

/-- The increasing map on the actual support agrees literally
with the prescribed old embedding, not with an abstract
isomorphism between the two induced support graphs. -/
@[simp] theorem partialSupportOrderIso_val
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V) (he : StrictMono e)
    (p : SupportCarrier U P) :
    (partialSupportOrderIso S P hP e he p).val =
      e ⟨p.val, hP p.property⟩ := by
  rfl

/-- Transport along a partial old map preserves the literal
size of the old support, including the empty-support case. -/
theorem partialSupportOrderIso_card
    (S P : Finset U) (hP : P ⊆ S)
    (e : SupportCarrier U S → V) (he : StrictMono e) :
    P.card = (CFNamedSupport.supportImage S P hP e).card := by
  classical
  have h := Fintype.card_congr
    (partialSupportOrderIso S P hP e he).toEquiv
  simpa only [Fintype.card_coe] using h

/-- Construct the actual bounded target C_F request over the
literal support image of a map defined only on the selected
old source. The partial map may have an empty codomain
when its source is empty. -/
noncomputable def transportGrowthStageRequest_partial
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U)
    (e : SupportCarrier U S → V) (he : StrictMono e)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩))
    (hClosed : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ) :
    StageRequest H (GrowthAllowedLocal F)
      (fun Q => K Q.card) := by
  classical
  let Q : Finset V :=
    CFNamedSupport.supportImage S r.support hSub e
  let iso : SupportCarrier U r.support ≃o SupportCarrier V Q :=
    partialSupportOrderIso S r.support hSub e he
  let baseP := supportGraph G r.support
  let baseQ := supportGraph H Q
  have hBase' : ∀ p q : SupportCarrier U r.support,
      baseP.adj p q ↔ baseQ.adj (iso p) (iso q) := by
    intro p q
    change G.adj p.val q.val ↔
      H.adj (iso p).val (iso q).val
    rw [partialSupportOrderIso_val, partialSupportOrderIso_val]
    exact hBase p q
  let localType : CFLocalCatalogue.OrderedLocalType
      (SupportCarrier V Q) baseQ
      (GrowthAllowedLocal F Q) r.code.1.val :=
    CFLocalCatalogue.namedBaseGrowthOrderedLocalType
      F baseP baseQ iso.toEquiv hBase' r.code.1.val r.code.2
  have hCard : r.support.card = Q.card :=
    partialSupportOrderIso_card S r.support hSub e he
  have hBound : r.code.1.val ≤ K Q.card := by
    rw [← hCard]
    exact Nat.lt_succ_iff.mp r.code.1.isLt
  exact ⟨Q, hClosed,
    CFLocalCatalogue.toBounded baseQ (GrowthAllowedLocal F Q)
      (K Q.card) r.code.1.val hBound localType⟩

/-- The target request retains the literal image of the
source support under the genuinely partial old map. -/
theorem transportGrowthStageRequest_partial_support
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U)
    (e : SupportCarrier U S → V) (he : StrictMono e)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩))
    (hClosed : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ) :
    (transportGrowthStageRequest_partial F K G H S e he
      r hSub hBase hClosed).support =
      CFNamedSupport.supportImage S r.support hSub e := rfl

/-- The constructed request has the same ordered fresh
block size; no new numerical bound or monotonicity of K
is needed. -/
theorem transportGrowthStageRequest_partial_size
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (G : GraphOn U) (H : GraphOn V)
    (S : Finset U)
    (e : SupportCarrier U S → V) (he : StrictMono e)
    (r : StageRequest G (GrowthAllowedLocal F)
      (fun P => K P.card))
    (hSub : r.support ⊆ S)
    (hBase : ∀ p q : SupportCarrier U r.support,
      G.adj p.val q.val ↔
        H.adj (e ⟨p.val, hSub p.property⟩)
          (e ⟨q.val, hSub q.property⟩))
    (hClosed : H.toPredimension.IsDClosed
      (CFNamedSupport.supportImage S r.support hSub e)
      Finset.univ) :
    (transportGrowthStageRequest_partial F K G H S e he
      r hSub hBase hClosed).code.1.val = r.code.1.val := rfl

end CFStageCatalogue
end BigHrushovski
