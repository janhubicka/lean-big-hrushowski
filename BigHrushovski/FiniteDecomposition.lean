import BigHrushovski.MinimalExtensions

/-!
# Finite decompositions into minimal strong extensions

Every finite globally strong extension A subset D can be refined into
minimal strong extensions. The proof is an induction on the number of
vertices not yet inserted and uses cardinal-minimal closure generators.

It does not claim an enumeration of the entire countable limit, which
additionally requires scheduling all finite extension requirements.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- No nontrivial intermediate strong substructure of a finite extension. -/
def IsMinimalStrongStep (d : Predimension V) (a b : Finset V) : Prop :=
  d.IsStrong a b ∧ a ≠ b ∧
    ∀ z : Finset V, a ⊆ z → z ⊆ b →
      d.IsStrong z b → z = a ∨ z = b

/-- A finite chain of minimal strong extensions, without encoding its length. -/
inductive MinimalStrongChain (d : Predimension V) :
    Finset V → Finset V → Prop where
  | refl (a : Finset V) : MinimalStrongChain d a a
  | step {a b c : Finset V}
      (hab : d.IsMinimalStrongStep a b)
      (hbc : MinimalStrongChain d b c) :
      MinimalStrongChain d a c

namespace StrongExhaustion

variable {d : Predimension V}

/-- Every finite extension between globally strong sets admits a
decomposition into minimal strong extensions. -/
theorem finite_minimal_decomposition (e : StrongExhaustion d) {a D : Finset V}
    (ha : d.IsGloballyStrong a)
    (hD : d.IsGloballyStrong D) (haD : a ⊆ D) :
    MinimalStrongChain d a D := by
  classical
  have core : ∀ n : ℕ, ∀ a : Finset V,
      d.IsGloballyStrong a → a ⊆ D →
      (D \ a).card = n → MinimalStrongChain d a D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a ha haD hn
        by_cases hnonempty : (D \ a).Nonempty
        · obtain ⟨v, hvD, hvna, hStep⟩ :=
            BigHrushovski.Predimension.StrongExhaustion.exists_minimal_strong_extension e ha hD haD hnonempty
          let B : Finset V := e.closure (insert v a)
          have hStep' : d.IsMinimalStrongStep a B := hStep
          have haB : a ⊆ B := hStep'.1.1
          have hBglobal : d.IsGloballyStrong B :=
            e.closure_global (insert v a)
          have hGenD : insert v a ⊆ D := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxa
            · exact hvD
            · exact haD hxa
          have hBD : B ⊆ D :=
            e.closure_least_global (insert v a) D hD hGenD
          have hDiffSub : D \ B ⊆ D \ a := by
            intro x hx
            have hxD := (Finset.mem_sdiff.mp hx).1
            have hxNotB := (Finset.mem_sdiff.mp hx).2
            exact Finset.mem_sdiff.mpr
              ⟨hxD, fun hxa => hxNotB (haB hxa)⟩
          have hvInDa : v ∈ D \ a :=
            Finset.mem_sdiff.mpr ⟨hvD, hvna⟩
          have hvNotDb : v ∉ D \ B := by
            intro hv
            have hvNotB := (Finset.mem_sdiff.mp hv).2
            exact hvNotB
              (e.subset_closure (insert v a)
                (Finset.mem_insert_self v a))
          have hDiffNe : D \ B ≠ D \ a := by
            intro heq
            have hvInDb : v ∈ D \ B := by
              rw [heq]
              exact hvInDa
            exact hvNotDb hvInDb
          have hProper : D \ B ⊂ D \ a :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hDiffSub, hDiffNe⟩
          have hLess : (D \ B).card < n := by
            have hCardLt := Finset.card_lt_card hProper
            rw [hn] at hCardLt
            exact hCardLt
          have hTail : MinimalStrongChain d B D :=
            ih (D \ B).card hLess B hBglobal hBD rfl
          exact MinimalStrongChain.step hStep' hTail
        · have hDa : D ⊆ a := by
            intro x hxD
            by_contra hxna
            exact hnonempty
              ⟨x, Finset.mem_sdiff.mpr ⟨hxD, hxna⟩⟩
          have hEq : a = D := le_antisymm haD hDa
          subst a
          exact MinimalStrongChain.refl D
  exact core (D \ a).card a ha haD rfl


/-- A finite strong extension in a globally strong ambient container can
be refined into minimal strong extensions. -/
theorem finite_minimal_decomposition_of_strong
    (e : StrongExhaustion d) {a D : Finset V}
    (hAD : d.IsStrong a D) (hD : d.IsGloballyStrong D) :
    MinimalStrongChain d a D :=
  e.finite_minimal_decomposition
    (d.globallyStrong_of_strong_in_global hAD hD) hD hAD.1

end StrongExhaustion
end Predimension
end BigHrushovski
