import BigHrushovski.CFArbitraryFiniteOneBlockUniqueness
import BigHrushovski.CFIntrinsicFiniteLevelAssignment

/-!
# Finite unique level lifting for the C_F block-support presentation

The one-block rigidity argument already shows that two arbitrary
finite embeddings with the same target birth level for a given
source vertex agree there, provided they agree below its source
birth level. We now apply strong induction on the actual birth
level, not on every stage of the finite tower and not on the
number of stages between represented source levels.

This yields uniqueness for any finite b-closed source under its
prescribed assignment of represented birth levels. Empty sources,
gaps in the source and target levels, and the first source level
mapping into target level zero require no exceptional treatment.
No increasing self-map of all of omega is assumed.

The equivalent finite R/H embedding statement follows by
translating the exact functional values to complete b-values.
Restriction/composition compatibility and the infinite embedding
monoid are separate consequences to be formalized after this step.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Two arbitrary finite b-functional embeddings preserving
the actual canonical order and level preorder agree pointwise
whenever they send each finite source vertex to the same
target birth level. No particular lift is chosen.

The proof is by strong induction on actual source birth
levels. The induction hypothesis concerns ONLY source
vertices born strictly earlier, not the whole old stage.
The source may be empty. -/
theorem arbitraryFiniteEmbedding_unique_of_targetLevels
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
    (hTargetLevels : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = (g x).1) :
    e = g := by
  funext x
  have hAll : ∀ n : ℕ,
      ∀ y : SupportCarrier (Vertex F K) s,
        y.val.1 = n → e y = g y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy
      rcases y with ⟨v, hv⟩
      rcases v with ⟨j, ⟨r, i⟩⟩
      change j = n at hy
      subst j
      let v : SupportCarrier (Vertex F K) s :=
        ⟨(⟨n, ⟨r, i⟩⟩ : Vertex F K), hv⟩
      have hOld : ∀ z : SupportCarrier (Vertex F K) s,
          z.val.1 < n → e z = g z := by
        intro z hz
        exact ih z.val.1 hz z rfl
      have hTargetLevel : (e v).1 = (g v).1 :=
        hTargetLevels v
      rcases heTarget : e v with ⟨m, ⟨t, k⟩⟩
      rcases hgTarget : g v with ⟨m', ⟨u, l⟩⟩
      have hm : m = m' := by
        simpa only [heTarget, hgTarget] using hTargetLevel
      subst m'
      have hEq : e v = g v :=
        arbitraryFiniteEmbedding_oneBlock_unique_at_target
          F K s hs e g heInj hgInj heAdj hgAdj heB hgB
          heLevel hgLevel heOrder hgOrder n r i hv m t u k l
          heTarget hgTarget hOld
      exact heTarget.symm.trans (hEq.trans hgTarget)
  exact hAll x.val.1 x rfl

/-- Every strictly increasing assignment of the finitely
represented source levels has AT MOST ONE finite b-functional
embedding with those exact target birth labels. The assignment
is unconstrained at unused source levels. -/
theorem arbitraryFiniteEmbedding_unique_of_prescribedLevels
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
    (heBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (e x).1 = level x.val.1)
    (hgBirth : ∀ x : SupportCarrier (Vertex F K) s,
      (g x).1 = level x.val.1) :
    e = g := by
  apply arbitraryFiniteEmbedding_unique_of_targetLevels
    F K s hs e g heInj hgInj heAdj hgAdj heB hgB
    heLevel hgLevel heOrder hgOrder
  intro x
  exact (heBirth x).trans (hgBirth x).symm

end CFCoherentTower
end BigHrushovski
