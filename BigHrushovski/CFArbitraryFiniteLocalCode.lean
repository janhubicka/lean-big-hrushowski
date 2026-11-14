import BigHrushovski.CFArbitraryFiniteSupportStageIso
import BigHrushovski.CFPartialStageSupportPointwise
import BigHrushovski.CFArbitraryFiniteFreshCoordinates
import BigHrushovski.CFArbitraryFiniteLocalInduced

/-!
# Complete local request code of an arbitrary finite C_F embedding

The previous lemmas provide all the ingredients of the actual
complete ordered request-code comparison for an arbitrary
embedding of a finite b-closed source:

* the exact literal target named support, and the increasing
  old-support order isomorphism, with its pointwise image;
* the exact fresh block size, and preservation of every fresh
  ordinal together with the target request tag;
* inducedness (preservation AND reflection of nonedges) on
  the entire old-support-plus-fresh-block local carrier.

We combine these with the previously verified full local
adjacency matrix transport theorem. In particular, no
abstractly isomorphic copy, total map of a complete source
stage, or globally increasing map of natural-number birth
levels is introduced.

This is the main one-block code ingredient for finite unique
level lifting. The represented-level uniqueness induction,
restriction/composition and countable monoid are still separate.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The unique increasing identification of finite ordinal
intervals of equal length is the identity on numerical values. -/
private noncomputable def finiteOrdinalIsoOfEq
    (a b : ℕ) (h : a = b) : Fin a ≃o Fin b := by
  cases h
  exact OrderIso.refl _

private theorem finiteOrdinalIsoOfEq_val
    (a b : ℕ) (h : a = b) (i : Fin a) :
    (finiteOrdinalIsoOfEq a b h i).val = i.val := by
  cases h
  rfl

/-- The complete ordered adjacency matrix of one source
request is unchanged by an ARBITRARY induced finite embedding
preserving the complete b-values, the birth-level preorder
and the canonical order. The target is the literal request
tag of the image of any chosen source fresh vertex.

Both edges and nonedges are compared, for old–old, old–fresh,
and fresh–fresh pairs. No target code equality is assumed;
it is derived from the embedding conditions. -/
theorem arbitraryFiniteEmbedding_requestAdjacencyCode
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s) :
    let w : Vertex F K :=
      e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    letI : LinearOrder (stage F K w.1).carrier :=
      stageLinearOrder F K w.1
    requestAdjacencyCode (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r =
    requestAdjacencyCode (stage F K w.1).graph
      (GrowthAllowedLocal F) (fun P => K P.card) w.2.1 := by
  classical
  let w : Vertex F K :=
    e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K w.1).carrier :=
    stageLinearOrder F K w.1
  have hP : r.support.image (toVertex F K n) ⊆ s := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    rw [← huv]
    exact (hs n r i hi).2 u hu
  have hImage :
      (selectedFiniteSet s
        (r.support.image (toVertex F K n))).image e =
        w.2.1.support.image (toVertex F K w.1) := by
    calc
      (selectedFiniteSet s
        (r.support.image (toVertex F K n))).image e =
          (selectedFiniteSet s
            (birthSupport F K n r)).image e := by
              rw [birthSupport_eq_stageSupport_image]
      _ = birthSupport F K w.1 w.2.1 :=
        (arbitraryFiniteEmbedding_support_block
          F K s e heB heLevel n r i hi).1
      _ = w.2.1.support.image (toVertex F K w.1) :=
        birthSupport_eq_stageSupport_image F K w.1 w.2.1
  let oldIso :
      SupportCarrier (stage F K n).carrier r.support ≃o
      SupportCarrier (stage F K w.1).carrier w.2.1.support :=
    arbitraryFiniteEmbedding_supportStageIso
      F K s hs e heB heLevel heOrder n r i hi
  have hSize : r.code.1.val = w.2.1.code.1.val :=
    arbitraryFiniteEmbedding_freshSize
      F K s hs e heInj heB heLevel n r i hi
  let freshIso : Fin r.code.1.val ≃o Fin w.2.1.code.1.val :=
    finiteOrdinalIsoOfEq r.code.1.val w.2.1.code.1.val hSize
  let hLocal : BirthRequestLocalCarrier F K n r → Vertex F K :=
    arbitraryFiniteEmbedding_localMap
      F K s hs e n r i hi
  have hTarget : ∀ a : BirthRequestLocalCarrier F K n r,
      hLocal a =
        birthRequestLocalVertex F K w.1 w.2.1
          (Sum.map oldIso freshIso a) := by
    intro a
    cases a with
    | inl u =>
        have hPoint :=
          finiteStageSupportOrderIso_apply_birth F K s n w.1
            r.support w.2.1.support hP e hImage heOrder u
        change
          e (finiteStageSupportPoint F K s n r.support hP u) =
            toVertex F K w.1 (oldIso u).val
        exact hPoint.symm
    | inr j =>
        have hj :
            (⟨n, ⟨r, j⟩⟩ : Vertex F K) ∈ s :=
          (hs n r i hi).1 j
        obtain ⟨k, hk, hkVal⟩ :=
          arbitraryFiniteEmbedding_freshCoordinate
            F K s hs e heB heLevel heOrder n r i hi j hj
        have hFreshVal :
            (freshIso j).val = j.val :=
          finiteOrdinalIsoOfEq_val
            r.code.1.val w.2.1.code.1.val hSize j
        have hK : k = freshIso j :=
          Fin.ext (hkVal.trans hFreshVal.symm)
        change
          e ⟨(⟨n, ⟨r, j⟩⟩ : Vertex F K), hj⟩ =
            (⟨w.1, ⟨w.2.1, freshIso j⟩⟩ : Vertex F K)
        rw [← hK]
        exact hk
  have hInduced : ∀ a b : BirthRequestLocalCarrier F K n r,
      (countableGraph F K).adj
        (birthRequestLocalVertex F K n r a)
        (birthRequestLocalVertex F K n r b) ↔
      (countableGraph F K).adj (hLocal a) (hLocal b) := by
    intro a b
    exact arbitraryFiniteEmbedding_localMap_induced
      F K s hs e heAdj n r i hi a b
  exact birthRequest_adjacencyCode_eq_of_partialInduced
    F K n w.1 r w.2.1 oldIso freshIso hLocal
    hTarget hInduced

end CFCoherentTower
end BigHrushovski
