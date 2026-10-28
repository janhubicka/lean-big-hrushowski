import BigHrushovski.CFCanonicalRequestRank
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Order.Sum.Order

/-!
# Coherent canonical orders on the actual C_F enumeration tower

The finite tower already has literal successor carriers
  U_(n+1) = U_n ⊕ (Σ request, Fin freshSize).
Here we put on each U_n the *particular* order in the manuscript.
The old part keeps its order and comes before every new vertex.
The fresh part is sorted by the exact lexicographic request rank,
then by the chosen finite ordinal within its request block.

The order is defined recursively, not chosen independently at each
stage. The rank of each request is the number of earlier literal
requests; in particular no arbitrary Fin equivalence enters the
construction. This is a concrete order on the actual stage carriers,
rather than an additional hypothetical order on an unrelated tower.

We also specialise the existing ranked birth order to the resulting
coherent ranks on these actual finite stages.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- Equip the ordinary sum carrier with its linear sum order:
all old vertices precede all new vertices, without changing
either summand's internal order. -/
noncomputable def lexSumLinearOrder
    (α β : Type*) [LinearOrder α] [LinearOrder β] :
    LinearOrder (Sum α β) :=
  LinearOrder.lift'
    (fun x : Sum α β => (toLex x : α ⊕ₗ β))
    (by
      intro x y h
      exact congrArg (ofLex : (α ⊕ₗ β) → Sum α β) h)

/-- The exact local order on request-tagged fresh vertices.
The first coordinate is the number of lexicographically earlier
literal requests, and the second is the chosen Fin ordinal. -/
noncomputable def freshRequestLinearOrder
    {U : Type*} [Fintype U] [LinearOrder U] [DecidableEq U]
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    LinearOrder (FreshCarrier G Allowed bound) := by
  classical
  let key : FreshCarrier G Allowed bound → ℕ ×ₗ ℕ :=
    fun x => toLex
      (requestLexRank G Allowed bound x.1, x.2.val)
  have hkey : Function.Injective key := by
    intro x y h
    rcases x with ⟨r, i⟩
    rcases y with ⟨s, j⟩
    change
      (toLex (requestLexRank G Allowed bound r, i.val) :
        ℕ ×ₗ ℕ) =
      toLex (requestLexRank G Allowed bound s, j.val) at h
    have hp :
        (requestLexRank G Allowed bound r, i.val) =
        (requestLexRank G Allowed bound s, j.val) :=
      congrArg (ofLex : (ℕ ×ₗ ℕ) → ℕ × ℕ) h
    have hrs : r = s :=
      requestLexRank_injective G Allowed bound (congrArg Prod.fst hp)
    cases hrs
    have hij : i = j := Fin.ext (congrArg Prod.snd hp)
    cases hij
    rfl
  exact LinearOrder.lift' key hkey

/-- The linear order recursively inherited by every finite C_F stage.
The old stage has the same order when viewed through Sum.inl;
all new request blocks follow the old part in exact request rank. -/
noncomputable def stageLinearOrder
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    (n : ℕ) → LinearOrder (stage F K n).carrier
  | 0 => by
      change LinearOrder (Fin 0)
      exact inferInstance
  | n + 1 => by
      classical
      letI : LinearOrder (stage F K n).carrier := stageLinearOrder F K n
      letI : LinearOrder (FreshAt F K n) :=
        freshRequestLinearOrder (stage F K n).graph
          (GrowthAllowedLocal F) (fun P => K P.card)
      change LinearOrder
        (Sum (stage F K n).carrier (FreshAt F K n))
      exact lexSumLinearOrder _ _

/-- The actual request ranks at the successive finite stages.
The order used on each stage is the recursively inherited one
above, rather than any unrelated finite order. -/
noncomputable def stageCanonicalRank
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    BirthRequestRanking F K := by
  intro n
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  exact requestLexRank (stage F K n).graph
    (GrowthAllowedLocal F) (fun P => K P.card)

/-- Each actual stage's canonical numerical request ranking
is injective on its literal dependent request records. -/
theorem stageCanonicalRank_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    ∀ n, Function.Injective (stageCanonicalRank F K n) := by
  intro n
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  change Function.Injective
    (requestLexRank (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card))
  exact requestLexRank_injective _ _ _

/-- This is exactly the prescribed finite request comparison,
at every stage with its *recursively inherited* old order. -/
theorem stageCanonicalRank_comparison
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (n : ℕ) (r s : BirthRequest F K n) :
    letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
    RequestLexLt (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r s ↔
    stageCanonicalRank F K n r < stageCanonicalRank F K n s := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  change
    RequestLexLt (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r s ↔
    requestLexRank (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) r <
    requestLexRank (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) s
  exact requestLexLt_iff_rank_lt _ _ _ r s

/-- The manuscript's countable birth order: birth level,
then the exact lexicographic request rank at that level,
then the chosen fresh-block ordinal. -/
noncomputable def canonicalBirthLt
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    Vertex F K → Vertex F K → Prop :=
  rankedBirthLt F K (stageCanonicalRank F K)

/-- The explicitly constructed order agrees with the chosen
finite ordered code inside every complete fresh block. -/
theorem canonicalBirthLt_compatible
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    BirthBlockOrderCompatible F K (canonicalBirthLt F K) :=
  rankedBirthLt_compatible F K (stageCanonicalRank F K)

/-- The actual canonical birth order is irreflexive. -/
theorem canonicalBirthLt_irrefl
    (F : ℕ → ℝ) (K : ℕ → ℕ) (v : Vertex F K) :
    ¬ canonicalBirthLt F K v v :=
  rankedBirthLt_irrefl F K (stageCanonicalRank F K) v

/-- The actual canonical birth order is transitive. -/
theorem canonicalBirthLt_trans
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (u v w : Vertex F K)
    (huv : canonicalBirthLt F K u v)
    (hvw : canonicalBirthLt F K v w) :
    canonicalBirthLt F K u w :=
  rankedBirthLt_trans F K (stageCanonicalRank F K) u v w huv hvw

/-- Any two distinct actual birth vertices are comparable. -/
theorem canonicalBirthLt_total
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (u v : Vertex F K) (huv : u ≠ v) :
    canonicalBirthLt F K u v ∨ canonicalBirthLt F K v u :=
  rankedBirthLt_total F K (stageCanonicalRank F K)
    (stageCanonicalRank_injective F K) u v huv

end CFCoherentTower
end BigHrushovski
