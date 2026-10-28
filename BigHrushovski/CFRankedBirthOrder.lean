import BigHrushovski.CFChosenOrderBridge

/-!
# Lexicographic order of tagged birth vertices from request rankings

The literal birth carrier consists of triples (level, request, fresh
ordinal). For a family of injective numerical ranks of the *finite*
request types, compare these triples lexicographically: first birth
level, then request rank at that level, and finally the fresh ordinal.

This gives a strict linear order and agrees exactly with the chosen
finite order on every birth block. In particular the complete b versus
(R,H) embedding theorem needs no additional root-selection order.

An arbitrary finite request ranking does NOT yet give the particular
lexicographic ordering of the *support tuples and adjacency codes*
chosen in the manuscript. The latter will be a separate specialization
of this generic construction. We record that remaining distinction
explicitly rather than silently identifying unrelated finite orders.
-/

namespace BigHrushovski
namespace CFCoherentTower

/-- One injective numerical rank for each finite set of level requests. -/
abbrev BirthRequestRanking (F : ℕ → ℝ) (K : ℕ → ℕ) :=
  (n : ℕ) → BirthRequest F K n → ℕ

/-- The numerical code of a literal tagged vertex. Every use
of an order on request tags passes through the supplied ranking. -/
def birthOrderKey
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K) :
    Vertex F K → ℕ × (ℕ × ℕ)
  | ⟨n, ⟨r, i⟩⟩ => (n, (rank n r, i.val))

/-- Lexicographic comparison of three natural numbers, in the
same convention as the manuscript for finite sequences. -/
def tripleLexLt (a b : ℕ × (ℕ × ℕ)) : Prop :=
  a.1 < b.1 ∨
  (a.1 = b.1 ∧
    (a.2.1 < b.2.1 ∨
      (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

theorem tripleLexLt_irrefl (a : ℕ × (ℕ × ℕ)) :
    ¬ tripleLexLt a a := by
  simp [tripleLexLt]

theorem tripleLexLt_trans
    (a b c : ℕ × (ℕ × ℕ))
    (hab : tripleLexLt a b) (hbc : tripleLexLt b c) :
    tripleLexLt a c := by
  rcases a with ⟨an, ⟨ar, ai⟩⟩
  rcases b with ⟨bn, ⟨br, bi⟩⟩
  rcases c with ⟨cn, ⟨cr, ci⟩⟩
  dsimp [tripleLexLt] at *
  omega

theorem tripleLexLt_trichotomy
    (a b : ℕ × (ℕ × ℕ)) :
    tripleLexLt a b ∨ a = b ∨ tripleLexLt b a := by
  rcases a with ⟨an, ⟨ar, ai⟩⟩
  rcases b with ⟨bn, ⟨br, bi⟩⟩
  dsimp [tripleLexLt]
  by_cases hn : an = bn
  · by_cases hr : ar = br
    · by_cases hi : ai = bi
      · right
        left
        simp [hn, hr, hi]
      · omega
    · omega
  · omega

/-- The actual birth order associated with numerical request ranks. -/
def rankedBirthLt
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K)
    (u v : Vertex F K) : Prop :=
  tripleLexLt (birthOrderKey F K rank u)
    (birthOrderKey F K rank v)

/-- The ordering always puts an earlier birth level first,
regardless of the chosen request ranking. -/
theorem rankedBirthLt_of_earlier
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K)
    (u v : Vertex F K) (h : u.1 < v.1) :
    rankedBirthLt F K rank u v := by
  exact Or.inl h

/-- The restriction to every complete request block agrees
with its chosen finite-ordinal order, independent of the
ordering of the other requests. -/
theorem rankedBirthLt_compatible
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K) :
    BirthBlockOrderCompatible F K (rankedBirthLt F K rank) := by
  classical
  intro v u w hu hw
  rcases v with ⟨n, ⟨r, k⟩⟩
  have hFresh :
      ∀ x : Vertex F K, x ∈ birthBlock F K n r →
        ∃ i : Fin r.code.1.val,
          x = (⟨n, ⟨r, i⟩⟩ : Vertex F K) := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    obtain ⟨i, _, hiz⟩ := Finset.mem_image.mp hz
    refine ⟨i, ?_⟩
    calc
      x = toVertex F K (n + 1) z := hzx.symm
      _ = toVertex F K (n + 1) (Sum.inr ⟨r, i⟩) := by
        rw [hiz]
      _ = (⟨n, ⟨r, i⟩⟩ : Vertex F K) := rfl
  obtain ⟨i, hi⟩ := hFresh u hu
  obtain ⟨j, hj⟩ := hFresh w hw
  subst u
  subst w
  simp [rankedBirthLt, tripleLexLt, birthOrderKey, birthOrdinal]

/-- If the request ranks are injective at each level, the
numerical triple code is injective on literal birth vertices. -/
theorem birthOrderKey_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K)
    (hRank : ∀ n : ℕ, Function.Injective (rank n)) :
    Function.Injective (birthOrderKey F K rank) := by
  intro u v h
  rcases u with ⟨n, ⟨r, i⟩⟩
  rcases v with ⟨m, ⟨q, j⟩⟩
  change (n, (rank n r, i.val)) =
    (m, (rank m q, j.val)) at h
  have hnm : n = m := congrArg Prod.fst h
  subst m
  have hr : rank n r = rank n q :=
    congrArg (fun p : ℕ × (ℕ × ℕ) => p.2.1) h
  have hrq : r = q := hRank n hr
  subst q
  have hij : i.val = j.val :=
    congrArg (fun p : ℕ × (ℕ × ℕ) => p.2.2) h
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

/-- The induced order is irreflexive. -/
theorem rankedBirthLt_irrefl
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K) (u : Vertex F K) :
    ¬ rankedBirthLt F K rank u u :=
  tripleLexLt_irrefl _

/-- Transitivity of the ranked birth order. -/
theorem rankedBirthLt_trans
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K)
    (u v w : Vertex F K)
    (huv : rankedBirthLt F K rank u v)
    (hvw : rankedBirthLt F K rank v w) :
    rankedBirthLt F K rank u w :=
  tripleLexLt_trans _ _ _ huv hvw

/-- Any two different birth vertices are comparable, provided
the chosen request rankings distinguish distinct request tags. -/
theorem rankedBirthLt_total
    (F : ℕ → ℝ) (K : ℕ → ℕ)
    (rank : BirthRequestRanking F K)
    (hRank : ∀ n : ℕ, Function.Injective (rank n))
    (u v : Vertex F K) (huv : u ≠ v) :
    rankedBirthLt F K rank u v ∨
      rankedBirthLt F K rank v u := by
  rcases tripleLexLt_trichotomy
      (birthOrderKey F K rank u) (birthOrderKey F K rank v)
    with hlt | heq | hgt
  · exact Or.inl hlt
  · exact False.elim (huv (birthOrderKey_injective F K rank hRank heq))
  · exact Or.inr hgt

/-- There is always some finite request ranking. This arbitrary
choice is convenient for testing the generic order construction,
but it is NOT identified with the manuscript's prescribed
lexicographic ordering of support tuples and local graph codes. -/
noncomputable def arbitraryRequestRank
    (F : ℕ → ℝ) (K : ℕ → ℕ) :
    BirthRequestRanking F K := by
  classical
  intro n
  letI : Fintype (BirthRequest F K n) := Fintype.ofFinite _
  exact fun r => ((Fintype.equivFin (BirthRequest F K n)) r).val

theorem arbitraryRequestRank_injective
    (F : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) :
    Function.Injective (arbitraryRequestRank F K n) := by
  classical
  letI : Fintype (BirthRequest F K n) := Fintype.ofFinite _
  intro r s h
  have hFin :
      ((Fintype.equivFin (BirthRequest F K n)) r).val =
      ((Fintype.equivFin (BirthRequest F K n)) s).val := h
  exact (Fintype.equivFin (BirthRequest F K n)).injective
    (Fin.ext hFin)

end CFCoherentTower
end BigHrushovski
