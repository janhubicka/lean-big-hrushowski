import BigHrushovski.CFRequestLexInjection

/-!
# Canonical numerical ranks of finite C_F requests

The manuscript compares *literal* requests at a finite stage by the
increasing tuple of the named support, the fresh size, and the complete
ordered adjacency matrix. The preceding modules prove that this is a
strict total order on the finite request catalogue.

For a request r, count the requests preceding r in this exact order.
This gives a numerical rank which is injective and both preserves and
reflects the prescribed request comparison. Unlike an arbitrary
equivalence with Fin, this rank is determined by the manuscript's order.

The old stage is assumed to have an inherited linear order. Constructing
those inherited orders coherently on the recursive finite tower, and
then identifying the corresponding birth order, remain separate tasks.
-/

namespace BigHrushovski
namespace CFStageCatalogue

variable {U : Type*}
variable [Fintype U] [LinearOrder U] [DecidableEq U]

/-- All literal requests strictly preceding a given request in the
precise support/fresh-size/adjacency-code order. -/
noncomputable def requestLexPredecessors
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) :
    Finset (StageRequest G Allowed bound) := by
  classical
  letI : Fintype (StageRequest G Allowed bound) := Fintype.ofFinite _
  exact Finset.univ.filter (fun s => RequestLexLt G Allowed bound s r)

theorem mem_requestLexPredecessors
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (s r : StageRequest G Allowed bound) :
    s ∈ requestLexPredecessors G Allowed bound r ↔
      RequestLexLt G Allowed bound s r := by
  classical
  simp [requestLexPredecessors]

/-- The rank of a literal request is the number of actual requests
preceding it under the prescribed finite lexicographic comparison. -/
noncomputable def requestLexRank
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r : StageRequest G Allowed bound) : ℕ :=
  (requestLexPredecessors G Allowed bound r).card

/-- Exact lexicographic comparison strictly increases the canonical
finite rank. This uses transitivity and irreflexivity, not an arbitrary
numbering of the request catalogue. -/
theorem requestLexRank_lt_of_lt
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    {r s : StageRequest G Allowed bound}
    (hrs : RequestLexLt G Allowed bound r s) :
    requestLexRank G Allowed bound r <
      requestLexRank G Allowed bound s := by
  classical
  have hsub :
      requestLexPredecessors G Allowed bound r ⊆
        requestLexPredecessors G Allowed bound s := by
    intro t ht
    apply (mem_requestLexPredecessors G Allowed bound t s).2
    exact requestLexLt_trans G Allowed bound t r s
      ((mem_requestLexPredecessors G Allowed bound t r).1 ht) hrs
  have hmem : r ∈ requestLexPredecessors G Allowed bound s :=
    (mem_requestLexPredecessors G Allowed bound r s).2 hrs
  have hnot : r ∉ requestLexPredecessors G Allowed bound r := by
    intro hr
    exact (requestLexLt_irrefl G Allowed bound r)
      ((mem_requestLexPredecessors G Allowed bound r r).1 hr)
  have hproper :
      requestLexPredecessors G Allowed bound r ⊂
        requestLexPredecessors G Allowed bound s :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨r, hmem, hnot⟩
  exact Finset.card_lt_card hproper

/-- The canonical request rank distinguishes all actual dependent
request records, including records with different named supports. -/
theorem requestLexRank_injective
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ) :
    Function.Injective (requestLexRank G Allowed bound) := by
  classical
  intro r s h
  rcases requestLexLt_trichotomy G Allowed bound r s with hlt | heq | hgt
  · have hlt' := requestLexRank_lt_of_lt G Allowed bound hlt
    omega
  · exact heq
  · have hgt' := requestLexRank_lt_of_lt G Allowed bound hgt
    omega

/-- Ranking is order-reflecting as well as order-preserving: numerical
comparison is equivalent to the exact lexicographic request order. -/
theorem requestLexLt_iff_rank_lt
    (G : GraphOn U) (Allowed : AllowedLocal U)
    (bound : Finset U → ℕ)
    (r s : StageRequest G Allowed bound) :
    RequestLexLt G Allowed bound r s ↔
      requestLexRank G Allowed bound r <
        requestLexRank G Allowed bound s := by
  constructor
  · exact requestLexRank_lt_of_lt G Allowed bound
  · intro hrank
    rcases requestLexLt_trichotomy G Allowed bound r s with hlt | heq | hgt
    · exact hlt
    · subst s
      exact False.elim (Nat.lt_irrefl _ hrank)
    · have hback := requestLexRank_lt_of_lt G Allowed bound hgt
      omega

end CFStageCatalogue
end BigHrushovski
