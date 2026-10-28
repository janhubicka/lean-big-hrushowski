import BigHrushovski.CFCanonicalOrderEmbedding

/-!
# Finite-level order coherence and rigidity of the C_F request tags

The recursive stage order introduced in CFCanonicalStageOrder is an
actual linear order, but the next level-lifting proof needs the *exact*
relations across the old and fresh summands. We expose them here.

The inclusion of the old stage is an order embedding. Every old
vertex precedes every new vertex. Among new vertices, the order is
exactly the manuscript's strict lexicographic comparison of complete
literal request codes, followed by the chosen ordinal within a block.

We also record a rigidity statement for the complete tag of a fresh
vertex. A support tuple, fresh size, full graph matrix and the
fresh ordinal determine a unique literal tagged vertex. This is the
finite uniqueness input for level lifting, not yet the lifting theorem.
-/

namespace BigHrushovski
namespace CFCoherentTower

open CFStageCatalogue

/-- The strict order on a finite stage, with the precise
recursively constructed linear-order instance supplied explicitly. -/
noncomputable def stageLt
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (u v : (stage F K n).carrier) : Prop := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  exact u < v

/-- Under the *actual recursively constructed orders*, the literal
old-stage embedding into its successor preserves and reflects <. -/
theorem stageOrder_old_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (u v : (stage F K n).carrier) :
    stageLt F K (n + 1) (Sum.inl u) (Sum.inl v) ↔
      stageLt F K n u v := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (FreshAt F K n) :=
    freshRequestLinearOrder (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
  change (toLex (Sum.inl u) :
    (stage F K n).carrier ⊕ₗ (FreshAt F K n)) <
    toLex (Sum.inl v) ↔ u < v
  exact Sum.Lex.inl_lt_inl_iff

/-- All old vertices precede *every* new vertex in the prescribed
successor order, including when its request catalogue is sparse. -/
theorem stageOrder_old_lt_fresh
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (u : (stage F K n).carrier) (v : FreshAt F K n) :
    stageLt F K (n + 1) (Sum.inl u) (Sum.inr v) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (FreshAt F K n) :=
    freshRequestLinearOrder (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
  change (toLex (Sum.inl u) :
    (stage F K n).carrier ⊕ₗ (FreshAt F K n)) <
    toLex (Sum.inr v)
  exact Sum.Lex.inl_lt_inr _ _

/-- Two fresh vertices in the successor stage are compared first by
their *exact* canonical request ranks, then by their chosen ordinals.
The old stage order used by these ranks is inherited recursively. -/
theorem stageOrder_fresh_iff
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r s : BirthRequest F K n)
    (i : Fin r.code.1.val) (j : Fin s.code.1.val) :
    stageLt F K (n + 1) (Sum.inr (⟨r, i⟩ : FreshAt F K n))
      (Sum.inr (⟨s, j⟩ : FreshAt F K n)) ↔
      stageCanonicalRank F K n r < stageCanonicalRank F K n s ∨
        (stageCanonicalRank F K n r =
           stageCanonicalRank F K n s ∧ i.val < j.val) := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  letI : LinearOrder (FreshAt F K n) :=
    freshRequestLinearOrder (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card)
  change
    (toLex (Sum.inr (⟨r, i⟩ : FreshAt F K n)) :
      (stage F K n).carrier ⊕ₗ (FreshAt F K n)) <
    toLex (Sum.inr (⟨s, j⟩ : FreshAt F K n)) ↔
    stageCanonicalRank F K n r < stageCanonicalRank F K n s ∨
      (stageCanonicalRank F K n r =
        stageCanonicalRank F K n s ∧ i.val < j.val)
  rw [Sum.Lex.inr_lt_inr_iff]
  change
    (toLex (stageCanonicalRank F K n r, i.val) : ℕ ×ₗ ℕ) <
      toLex (stageCanonicalRank F K n s, j.val) ↔
    stageCanonicalRank F K n r < stageCanonicalRank F K n s ∨
      (stageCanonicalRank F K n r =
        stageCanonicalRank F K n s ∧ i.val < j.val)
  exact Prod.Lex.toLex_lt_toLex

/-- The exact numerical request comparison in the successor order
is the manuscript's support-tuple/fresh-size/matrix comparison. -/
theorem stageOrder_fresh_of_requestLexLt
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (r s : BirthRequest F K n)
    (i : Fin r.code.1.val) (j : Fin s.code.1.val)
    (h : letI : LinearOrder (stage F K n).carrier :=
        stageLinearOrder F K n
      RequestLexLt (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) r s) :
    stageLt F K (n + 1) (Sum.inr (⟨r, i⟩ : FreshAt F K n))
      (Sum.inr (⟨s, j⟩ : FreshAt F K n)) := by
  apply (stageOrder_fresh_iff F K n r s i j).2
  exact Or.inl ((stageCanonicalRank_comparison F K n r s).mp h)

/-- Equality of the *whole* finite request key and the fresh ordinal
identifies one literal tagged vertex. Mere equality of support sizes
or adjacency degree sequences would not be sufficient. -/
theorem freshVertex_eq_of_completeCode
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (a b : FreshAt F K n)
    (hKey : letI : LinearOrder (stage F K n).carrier :=
      stageLinearOrder F K n
      requestLexKey (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) a.1 =
      requestLexKey (stage F K n).graph
        (GrowthAllowedLocal F) (fun P => K P.card) b.1)
    (hOrdinal : a.2.val = b.2.val) :
    a = b := by
  letI : LinearOrder (stage F K n).carrier :=
    stageLinearOrder F K n
  have hReq : a.1 = b.1 :=
    requestLexKey_injective (stage F K n).graph
      (GrowthAllowedLocal F) (fun P => K P.card) hKey
  rcases a with ⟨r, i⟩
  rcases b with ⟨s, j⟩
  change r = s at hReq
  cases hReq
  have hij : i = j := Fin.ext hOrdinal
  cases hij
  rfl

end CFCoherentTower
end BigHrushovski
