import BigHrushovski.CFArbitraryFiniteLocalCode
import BigHrushovski.CFArbitraryFiniteTargetSupportAgreement
import BigHrushovski.CFBirthRequestTagRecognition

/-!
# Uniqueness of an arbitrary finite C_F lift at one birth block

Suppose two embeddings of the same finite b-closed source agree on
every vertex born before n, and send a given source vertex born at n
to a common target birth level m. The full named target support is
then the same for both embeddings. The induced complete ordered
local graph, together with the exact fresh size, determines the
same literal target request tag. Finally the canonical order fixes
the ordinal of the vertex within its block.

This is the one-block step of the finite unique level-lifting lemma,
not merely rigidity of the specially constructed lift. It makes no
assumption about a map of the whole old stage and admits empty old
supports and target stage U_0. The induction over levels is separate.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Two arbitrary admissible finite embeddings with identical old
source images and with the same target birth level for one vertex
must have the same image of that vertex. Target request tags and
fresh ordinals are NOT prescribed as hypotheses: their equality
is obtained from complete support, size and matrix equality.

The two target vertices are written with their actual request
coordinates at a COMMON target stage m. This avoids assuming a
globally increasing map on source or target birth levels. -/
theorem arbitraryFiniteEmbedding_oneBlock_unique_at_target
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (e g : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (hgInj : Function.Injective g)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (hgAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (g x) (g y))
    (heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x))
    (hgB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image g =
        birthBValue F K (g x))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (hgLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (g x) (g y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (hgOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (g x) (g y))
    (n : ℕ) (r : BirthRequest F K n)
    (i : Fin r.code.1.val)
    (hi : (⟨n, ⟨r, i⟩⟩ : Vertex F K) ∈ s)
    (m : ℕ) (t u : BirthRequest F K m)
    (k : Fin t.code.1.val) (l : Fin u.code.1.val)
    (heTarget :
      e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ =
        (⟨m, ⟨t, k⟩⟩ : Vertex F K))
    (hgTarget :
      g ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ =
        (⟨m, ⟨u, l⟩⟩ : Vertex F K))
    (hOld : ∀ x : SupportCarrier (Vertex F K) s,
      x.val.1 < n → e x = g x) :
    e ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ =
      g ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩ := by
  classical
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (stage F K m).carrier :=
    stageLinearOrder F K m
  let x : SupportCarrier (Vertex F K) s :=
    ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hi⟩
  have hSupportBirth :=
    arbitraryFiniteEmbedding_targetSupport_agree_of_old
      F K s e g heB hgB heLevel hgLevel n r i i hi hi hOld
  change
    birthSupport F K (e x).1 (e x).2.1 =
      birthSupport F K (g x).1 (g x).2.1 at hSupportBirth
  rw [heTarget, hgTarget] at hSupportBirth
  have hSupport : t.support = u.support :=
    birthRequest_support_eq_of_birthSupport_eq
      F K m t u hSupportBirth
  have hSizeE :=
    arbitraryFiniteEmbedding_freshSize
      F K s hs e heInj heB heLevel n r i hi
  have hSizeG :=
    arbitraryFiniteEmbedding_freshSize
      F K s hs g hgInj hgB hgLevel n r i hi
  change r.code.1.val = (e x).2.1.code.1.val at hSizeE
  change r.code.1.val = (g x).2.1.code.1.val at hSizeG
  rw [heTarget] at hSizeE
  rw [hgTarget] at hSizeG
  have hSize : t.code.1.val = u.code.1.val :=
    hSizeE.symm.trans hSizeG
  have hCodeE :=
    arbitraryFiniteEmbedding_requestAdjacencyCode
      F K s hs e heInj heAdj heB heLevel heOrder n r i hi
  have hCodeG :=
    arbitraryFiniteEmbedding_requestAdjacencyCode
      F K s hs g hgInj hgAdj hgB hgLevel hgOrder n r i hi
  change
    requestAdjacencyCode (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r =
    requestAdjacencyCode (stage F K (e x).1).graph
      (GrowthAllowedLocal F) (fun P => K P.card) (e x).2.1
      at hCodeE
  change
    requestAdjacencyCode (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r =
    requestAdjacencyCode (stage F K (g x).1).graph
      (GrowthAllowedLocal F) (fun P => K P.card) (g x).2.1
      at hCodeG
  rw [heTarget] at hCodeE
  rw [hgTarget] at hCodeG
  have hTag : t = u :=
    request_eq_of_support_size_adjacency
      (stage F K m).graph (GrowthAllowedLocal F)
      (fun P => K P.card) t u
      hSupport hSize (hCodeE.symm.trans hCodeG)
  subst u
  have hOrdE :=
    arbitraryFiniteEmbedding_birthOrdinal
      F K s hs e heB heLevel heOrder x
  have hOrdG :=
    arbitraryFiniteEmbedding_birthOrdinal
      F K s hs g hgB hgLevel hgOrder x
  change birthOrdinal F K (e x) = i.val at hOrdE
  change birthOrdinal F K (g x) = i.val at hOrdG
  rw [heTarget] at hOrdE
  rw [hgTarget] at hOrdG
  change k.val = i.val at hOrdE
  change l.val = i.val at hOrdG
  have hOrdinal : k = l :=
    Fin.ext (hOrdE.trans hOrdG.symm)
  subst l
  exact heTarget.trans hgTarget.symm

end CFCoherentTower
end BigHrushovski
