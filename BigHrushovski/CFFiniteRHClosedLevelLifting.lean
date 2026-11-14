import BigHrushovski.CFPrescribedFiniteRHRestriction
import BigHrushovski.CFRHClosedSubstructures
import BigHrushovski.CFFiniteClosedImageNaturality

/-!
# Finite prescribed-level lifts on genuine R/H-substructures

The paper states the finite unique-lifting lemma for finite
substructures in the actual (R,H) language. The previous finite
existence-and-uniqueness theorem has a finite complete-b-closed
source as its input. The two closure conditions are equivalent,
but that equivalence must be invoked explicitly at the theorem
interface rather than silently treating any finite vertex set
as a functional substructure.

We also prove that *any* finite R/H-embedding with the exact
partial-operation properties has a finite R/H-closed image.
This uses the already verified R/H-to-complete-b translation,
not only graph inducedness or transport of named roots.

No assumption about globally increasing level maps or countable
embeddings is used.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Being a finite substructure in the actual R,H language:
closure under every R-value and under H wherever its input is a
finite set of roots. In particular, H is NOT regarded as total. -/
def IsFiniteRHClosed (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) : Prop :=
  IsRHClosedSet F K {v | v ∈ s}

/-- Genuine finite R,H-substructures are exactly finite
complete-b-closed subsets of the actual birth carrier.
The right-hand predicate is the one used by the recursive
finite lifting theorem. Both directions use the existing
recovery theorem H(R(v)) = C(v); mere root closure would not
suffice. -/
theorem finiteRHClosed_iff_birthBlockClosed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K)) :
    IsFiniteRHClosed F K s ↔ IsBirthBlockClosed F K s := by
  change IsRHClosedSet F K {v | v ∈ s} ↔
    IsBirthBlockClosedSet F K {v | v ∈ s}
  exact (birthBlockClosedSet_iff_rhClosed F K {v | v ∈ s}).symm

/-- A finite prescribed-level embedding in the manuscript's
genuine R,H language: complete induced graph, prescribed birth
labels, the level preorder, the canonical linear order, exact
R-values and all *defined* H-values with reflection of the
partial domain of H. -/
def FiniteRHLevelEmbedding
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (level : ℕ → ℕ)
    (e : SupportCarrier (Vertex F K) s → Vertex F K) : Prop :=
  Function.Injective e ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    (countableGraph F K).adj x.val y.val ↔
      (countableGraph F K).adj (e x) (e y)) ∧
  (∀ x : SupportCarrier (Vertex F K) s,
    (e x).1 = level x.val.1) ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    BirthLevelLe F K x.val y.val ↔
      BirthLevelLe F K (e x) (e y)) ∧
  (∀ x y : SupportCarrier (Vertex F K) s,
    canonicalBirthLt F K x.val y.val ↔
      canonicalBirthLt F K (e x) (e y)) ∧
  FiniteSourceRHValues F K s e

/-- Exact manuscript-facing unique lifting theorem. Any finite
R,H-substructure and any strictly increasing assignment on
its *represented* birth levels admit exactly one induced,
ordered, R/H-preserving embedding realizing those labels.

This includes the empty source, arbitrarily skipped source
and target levels, and a first represented level mapped to
target level zero. The embedding is not required to be an
extension of a full old-stage embedding. -/
theorem finiteRHClosed_existsUnique_levelLift
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (level : ℕ → ℕ)
    (hStrict : StrictOnRepresented F K s level) :
    ∃! e : SupportCarrier (Vertex F K) s → Vertex F K,
      FiniteRHLevelEmbedding F K s level e := by
  have hsB : IsBirthBlockClosed F K s :=
    (finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH
  exact finiteSourcePrescribedLift_existsUnique_RH
    F K s hsB level hStrict

/-- For arbitrary finite embeddings of genuine R/H-substructures,
the LITERAL finite image is again closed under R and under every
defined H-value. We do not impose the prescribed target-level
assignment: preservation and reflection of the level preorder,
the canonical order and the actual R/H operations suffice.

This asserts closure of the full image, not just inclusion of
the named supports of its vertices. -/
theorem finiteRHEmbedding_image_closed
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (s : Finset (Vertex F K))
    (hsRH : IsFiniteRHClosed F K s)
    (e : SupportCarrier (Vertex F K) s → Vertex F K)
    (heInj : Function.Injective e)
    (heAdj : ∀ x y : SupportCarrier (Vertex F K) s,
      (countableGraph F K).adj x.val y.val ↔
        (countableGraph F K).adj (e x) (e y))
    (heLevel : ∀ x y : SupportCarrier (Vertex F K) s,
      BirthLevelLe F K x.val y.val ↔
        BirthLevelLe F K (e x) (e y))
    (heOrder : ∀ x y : SupportCarrier (Vertex F K) s,
      canonicalBirthLt F K x.val y.val ↔
        canonicalBirthLt F K (e x) (e y))
    (heRH : FiniteSourceRHValues F K s e) :
    IsFiniteRHClosed F K (finiteBirthSourceImage F K s e) := by
  have hsB : IsBirthBlockClosed F K s :=
    (finiteRHClosed_iff_birthBlockClosed F K s).mp hsRH
  have heB : ∀ x : SupportCarrier (Vertex F K) s,
      (finiteSourceBirthBValue F K s x).image e =
        birthBValue F K (e x) :=
    arbitraryFiniteRHEmbedding_completeB
      F K s hsB e heInj heAdj heLevel heOrder heRH
  exact (finiteRHClosed_iff_birthBlockClosed
    F K (finiteBirthSourceImage F K s e)).mpr
      (finiteBirthSourceImage_bClosed F K s e heB)

end CFCoherentTower
end BigHrushovski
