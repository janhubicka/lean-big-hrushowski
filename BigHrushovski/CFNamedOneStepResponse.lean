import BigHrushovski.CFCompleteOneBlockResponse
import BigHrushovski.CFTransportedBoundary
import BigHrushovski.CFPrescribedClosedSupport
import BigHrushovski.CFGrowthNormalizedLocal

/-!
# A globally d-closed response to a bounded named C_F local extension

This theorem composes four independently certified finite interfaces:
the literal closed support of a prescribed old embedding,
growth-preserving relabelling over that support, increasing
normalization of a fresh ordered block, and the complete induced
one-block response inside the countable tagged C_F graph.

The input is a minimal local extension already expressed over its
canonical old support P. Its complete graph is on P ⊕ B; the
larger old source S is still present and is embedded by a fixed map f.
We construct the actual request in the stage catalogue over
Q=f[P]. The new embedding of S ⊕ Fin(card B) retains every
source vertex's birth label, has the exact complete adjacency
relation, and has a globally strictly d-closed finite image.

The local minimality, canonical support, C_F membership and
numerical cardinality bound remain *explicit* hypotheses.
Deriving those hypotheses from an arbitrary abstract minimal
extension A <_d C is the separate final decomposition bridge.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue CFLocalCatalogue

variable {S B : Type*} [Fintype S] [DecidableEq S]
variable [LinearOrder B] [Fintype B] [DecidableEq B]

/-- For a fixed injective map f and a finite actual support P,
there is a unique literal equivalence from P to its image f[P].
Unlike an arbitrary isomorphism, its underlying values agree
pointwise with the prescribed old map f. -/
noncomputable def oldSupportImageEquiv
    {U : Type*} [DecidableEq U]
    (f : S → U) (hf : Function.Injective f)
    (P : Finset S) :
    {s : S // s ∈ P} ≃ {u : U // u ∈ P.image f} := by
  classical
  let phi : {s : S // s ∈ P} → {u : U // u ∈ P.image f} :=
    fun p => ⟨f p.val,
      Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
  refine Equiv.ofBijective phi ⟨?_, ?_⟩
  · intro p q hpq
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hpq
  · intro q
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp q.property
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    exact hsq

@[simp] theorem oldSupportImageEquiv_val
    {U : Type*} [DecidableEq U]
    (f : S → U) (hf : Function.Injective f)
    (P : Finset S) (p : {s : S // s ∈ P}) :
    (oldSupportImageEquiv f hf P p).val = f p.val := by
  rfl

/-- Respond globally to a fully specified minimal local extension
over the actual named support Q=f[P] while keeping the *whole*
prescribed old source S fixed pointwise. In particular, all
old-fresh nonedges outside P are reflected, rather than assumed.

The fresh size bound is the sole numerical input. The theorem
does not assume the requested extension already embeds into a
later stage; it constructs the new map from the finite catalogue. -/
theorem namedLocalExtension_globalResponse
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (H : GraphOn (Sum S B))
    (f : S → (stage F K n).carrier)
    (hf : Function.Injective f)
    (hOld : ∀ x y : S,
      H.adj (Sum.inl x) (Sum.inl y) ↔
        (stage F K n).graph.adj (f x) (f y))
    (hSourceClosed : (stage F K n).graph.toPredimension.IsDClosed
      ((Finset.univ : Finset S).image f) Finset.univ)
    (P : Finset S)
    (hP : (H.pullback Sum.inl).toPredimension.IsDClosed
      P Finset.univ)
    (hLocalGrowth :
      (oldSubsetLocalGraph H P).IsGrowthSparse F Finset.univ)
    (hLocalMinimal :
      (oldSubsetLocalGraph H P).toPredimension.IsMinimalDClosedStep
        (actualOld {s : S // s ∈ P} B) Finset.univ)
    (hLocalSupport :
      (oldSubsetLocalGraph H P).toPredimension.dClosedHull
        ((oldSubsetLocalGraph H P).oldNeighbourSet
          (actualOld {s : S // s ∈ P} B)
          (actualFresh {s : S // s ∈ P} B))
        (actualOld {s : S // s ∈ P} B) =
          actualOld {s : S // s ∈ P} B)
    (hBack : ∀ x : S, ∀ b : B,
      H.adj (Sum.inl x) (Sum.inr b) → x ∈ P)
    (hSize : Fintype.card B ≤ K (P.image f).card) :
    ∃ g : Sum S (Fin (Fintype.card B)) → Vertex F K,
      Function.Injective g ∧
      (∀ x : S, g (Sum.inl x) = toVertex F K n (f x)) ∧
      (∀ x y : Sum S (Fin (Fintype.card B)),
        (H.pullback
          (Equiv.sumCongr (Equiv.refl S)
            (increasingNewBlock (B := B)).toEquiv)).adj x y ↔
          (countableGraph F K).adj (g x) (g y)) ∧
      (countableGraph F K).toPredimension.IsGloballyDClosed
        ((Finset.univ : Finset (Sum S (Fin (Fintype.card B)))).image g) := by
  classical
  let G := (stage F K n).graph
  let Q : Finset (stage F K n).carrier := P.image f
  let e := oldSupportImageEquiv f hf P
  have heVal : ∀ p : {s : S // s ∈ P},
      (e p).val = f p.val := by
    intro p
    rfl
  have hQClosed : G.toPredimension.IsDClosed Q Finset.univ :=
    inducedSource_namedSupport_dClosed F K n
      (H.pullback Sum.inl) f hf hOld hSourceClosed P hP
  have hQsub : Q ⊆ ((Finset.univ : Finset S).image f) :=
    Finset.image_mono f (Finset.subset_univ P)
  let L := oldSubsetLocalGraph H P
  let baseP : GraphOn {s : S // s ∈ P} :=
    (H.pullback Sum.inl).pullback Subtype.val
  let baseQ := supportGraph G Q
  have hLocalOld : ∀ p q : {s : S // s ∈ P},
      L.adj (Sum.inl p) (Sum.inl q) ↔ baseP.adj p q := by
    intro p q
    rfl
  have hBase : ∀ p q : {s : S // s ∈ P},
      baseP.adj p q ↔ baseQ.adj (e p) (e q) := by
    intro p q
    change H.adj (Sum.inl p.val) (Sum.inl q.val) ↔
      G.adj (e p).val (e q).val
    simpa only [heVal p, heVal q] using hOld p.val q.val
  let J := namedBaseGraph e L
  have hJOld : ∀ q r : SupportCarrier (stage F K n).carrier Q,
      J.adj (Sum.inl q) (Sum.inl r) ↔ baseQ.adj q r := by
    intro q r
    exact namedBase_old_adj_iff e L baseP baseQ
      hLocalOld hBase q r
  have hJGrowth : J.IsGrowthSparse F Finset.univ :=
    (namedBase_growthSparse_iff F e L).mpr hLocalGrowth
  have hJMinimal : J.toPredimension.IsMinimalDClosedStep
      (actualOld (SupportCarrier (stage F K n).carrier Q) B)
      Finset.univ :=
    (namedBase_minimal_iff e L).mpr hLocalMinimal
  have hJSupport : J.toPredimension.dClosedHull
      (J.oldNeighbourSet
        (actualOld (SupportCarrier (stage F K n).carrier Q) B)
        (actualFresh (SupportCarrier (stage F K n).carrier Q) B))
      (actualOld (SupportCarrier (stage F K n).carrier Q) B) =
      (actualOld (SupportCarrier (stage F K n).carrier Q) B) :=
    (namedBase_exactSupport_iff e L).mpr hLocalSupport
  let t : OrderedLocalType
      (SupportCarrier (stage F K n).carrier Q) baseQ
      (GrowthAllowedLocal F Q) (Fintype.card B) :=
    growthLocalType_of_orderedGraph F baseQ J
      hJOld hJGrowth hJMinimal hJSupport
  let allowed : AllowedLocal (stage F K n).carrier :=
    GrowthAllowedLocal F
  let bound : Finset (stage F K n).carrier → ℕ :=
    fun R => K R.card
  let r := requestOfOrderedLocal G allowed bound
    Q hQClosed (Fintype.card B) hSize t
  let Hnorm : GraphOn (Sum S (Fin (Fintype.card B))) :=
    H.pullback
      (Equiv.sumCongr (Equiv.refl S)
        (increasingNewBlock (B := B)).toEquiv)
  have hNormOld : ∀ x y : S,
      Hnorm.adj (Sum.inl x) (Sum.inl y) ↔ G.adj (f x) (f y) := by
    intro x y
    exact hOld x y
  have hNormFresh : ∀ i j : Fin (Fintype.card B),
      Hnorm.adj (Sum.inr i) (Sum.inr j) ↔
        r.code.2.graph.adj (Sum.inr i) (Sum.inr j) := by
    intro i j
    change H.adj
      (Sum.inr (increasingNewBlock (B := B) i))
      (Sum.inr (increasingNewBlock (B := B) j)) ↔
        (transportedLocalGraph H P e).adj (Sum.inr i) (Sum.inr j)
    exact (transportedLocal_fresh_iff H P e i j).symm
  have hNormBoundary : ∀ x : S, ∀ i : Fin (Fintype.card B),
      Hnorm.adj (Sum.inl x) (Sum.inr i) ↔
        ∃ q : SupportCarrier (stage F K n).carrier r.support,
          q.val = f x ∧
          r.code.2.graph.adj (Sum.inl q) (Sum.inr i) := by
    intro x i
    change H.adj (Sum.inl x)
      (Sum.inr (increasingNewBlock (B := B) i)) ↔
      ∃ q : SupportCarrier (stage F K n).carrier Q,
        q.val = f x ∧
        (transportedLocalGraph H P e).adj
          (Sum.inl q) (Sum.inr i)
    exact transportedLocal_full_boundary_iff H P Q f hf e
      heVal hBack x i
  exact completeOneBlock_global F K n f hf r Hnorm
    hNormOld hNormFresh hNormBoundary hSourceClosed hQsub

end CFCoherentTower
end BigHrushovski
