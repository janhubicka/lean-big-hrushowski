import BigHrushovski.CFArbitraryFiniteUniqueness
import BigHrushovski.CFArbitraryFiniteFreshSize

/-!
# Finite unique level lifting in the manuscript's (R,H) language

The auxiliary complete b-value is equivalent, on a b-closed
finite source, to the actual root operation R and the partial
hull operation H, including reflection of H's domain.
The arbitrary finite b-functional uniqueness theorem therefore
gives uniqueness directly for arbitrary embeddings in the
manuscript's genuine (R,H) functional language.

Neither map is required to be the specially constructed
finite lift, and no global map of all birth levels is assumed.
The source can be empty, and its represented levels can have
arbitrary gaps. This is uniqueness (at most one embedding);
existence is the previously verified prescribed finite lift.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Two arbitrary finite (R,H)-embeddings, preserving the
complete graph, actual canonical order and birth-level preorder,
are literally equal whenever they realize the same prescribed
target birth level at each source vertex.

H is a PARTIAL operation. Both maps preserve its values
where defined and reflect its domain. Full b-values are
derived using the verified closed-source equivalence and
are not assumed independently. -/
theorem arbitraryFiniteRHEmbedding_unique_of_prescribedLevels
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hs : IsBirthBlockClosed F K s)
    (level : ℕ → ℕ)
    (e g : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (hgInj : Function.Injective g)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (hgAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (g x) (g y))
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
    (heRH :
      let X : Set (Vertex F K) := {v | v ∈ s}
      let f := extendClosedSourceMap F K X e
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        (∀ r ∈ t, IsBirthRoot F K r) →
        (birthDClosedHull F K t).image f =
          birthDClosedHull F K (t.image f)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        ((∀ r ∈ t, IsBirthRoot F K r) ↔
          (∀ r ∈ t.image f, IsBirthRoot F K r))))
    (hgRH :
      let X : Set (Vertex F K) := {v | v ∈ s}
      let f := extendClosedSourceMap F K X g
      (∀ v ∈ X,
        (birthReachableRoots F K v).image f =
          birthReachableRoots F K (f v)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        (∀ r ∈ t, IsBirthRoot F K r) →
        (birthDClosedHull F K t).image f =
          birthDClosedHull F K (t.image f)) ∧
      (∀ t : Finset (Vertex F K),
        (∀ v ∈ t, v ∈ X) →
        ((∀ r ∈ t, IsBirthRoot F K r) ↔
          (∀ r ∈ t.image f, IsBirthRoot F K r))))
    (heBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1)
    (hgBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (g x).1 = level x.val.1) :
    e = g := by
  have heB :
      ∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image e =
          birthBValue F K (e x) :=
    arbitraryFiniteRHEmbedding_completeB
      F K s hs e heInj heAdj heLevel heOrder heRH
  have hgB :
      ∀ x : SupportCarrier (Vertex F K) s,
        (finiteSourceBirthBValue F K s x).image g =
          birthBValue F K (g x) :=
    arbitraryFiniteRHEmbedding_completeB
      F K s hs g hgInj hgAdj hgLevel hgOrder hgRH
  exact arbitraryFiniteEmbedding_unique_of_prescribedLevels
    F K s hs level e g heInj hgInj heAdj hgAdj heB hgB
    heLevel hgLevel heOrder hgOrder heBirth hgBirth

end CFCoherentTower
end BigHrushovski
