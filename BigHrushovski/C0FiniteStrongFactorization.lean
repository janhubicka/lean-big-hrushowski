import BigHrushovski.FiniteDecomposition

/-!
# Finite strong extensions decompose without a strong exhaustion

For a finite strong inclusion A ≤ B, choose a strong intermediate set
C with A ⊊ C ≤ B having the smallest cardinality. No intermediate
set strictly between A and C can be strong in C, because it would
also be strong in B. Thus A < C is a minimal strong step.

Iterating this argument on the strictly smaller set B \ C gives a
finite minimal-strong chain from A to B.

Unlike the earlier StrongExhaustion.finite_minimal_decomposition,
this proof does not assume that A or B is globally strong in any
larger graph. That is the natural finite decomposition needed when
functional strong graph extensions are formed before their countable
Fraïssé limit has been constructed.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- Every proper finite strong extension A ≤ B has a first
minimal strong step A < C with C ≤ B. -/
theorem exists_minimalStrongStep_of_strong
    {a b : Finset V}
    (hab : d.IsStrong a b) (hne : a ≠ b) :
    ∃ c : Finset V,
      d.IsMinimalStrongStep a c ∧ d.IsStrong c b := by
  classical
  let candidates : Finset (Finset V) :=
    b.powerset.filter (fun c => a ⊂ c ∧ d.IsStrong c b)
  have hProper : a ⊂ b :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hab.1, hne⟩
  have hBCand : b ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hProper, d.strong_refl b⟩
  let sizes : Finset ℕ := candidates.image Finset.card
  have hSizes : sizes.Nonempty := by
    exact ⟨b.card, Finset.mem_image.mpr ⟨b, hBCand, rfl⟩⟩
  have hMinMem : sizes.min' hSizes ∈ sizes :=
    Finset.min'_mem sizes hSizes
  obtain ⟨c, hcCand, hcEq⟩ := Finset.mem_image.mp hMinMem
  obtain ⟨hcB, hAc, hcStrong⟩ :
      c ⊆ b ∧ a ⊂ c ∧ d.IsStrong c b := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset]
      using hcCand
  have hac : a ⊆ c :=
    (Finset.ssubset_iff_subset_ne.mp hAc).1
  have hacNe : a ≠ c :=
    (Finset.ssubset_iff_subset_ne.mp hAc).2
  have hacStrong : d.IsStrong a c :=
    d.strong_restrict hab hac hcB
  have hMinimal : d.IsMinimalStrongStep a c := by
    refine ⟨hacStrong, hacNe, ?_⟩
    intro z haz hzc hzStrong
    by_cases hEqA : z = a
    · exact Or.inl hEqA
    · right
      have hAZ : a ⊂ z :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨haz, by intro heq; exact hEqA heq.symm⟩
      have hzStrongB : d.IsStrong z b :=
        d.strong_trans hzStrong hcStrong
      have hzCand : z ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hzc.trans hcB, hAZ, hzStrongB⟩
      have hzSize : z.card ∈ sizes :=
        Finset.mem_image.mpr ⟨z, hzCand, rfl⟩
      have hCard : c.card ≤ z.card := by
        rw [hcEq]
        exact Finset.min'_le sizes z.card hzSize
      exact Finset.eq_of_subset_of_card_le hzc hCard
  exact ⟨c, hMinimal, hcStrong⟩

/-- Every finite strong inclusion A ≤ B admits a finite chain of
minimal strong steps. No ambient strong-exhaustion hypothesis is used. -/
theorem finite_minimal_decomposition_of_strong_absolute
    {a b : Finset V}
    (hab : d.IsStrong a b) :
    MinimalStrongChain d a b := by
  classical
  have core : ∀ n : ℕ, ∀ a : Finset V,
      d.IsStrong a b →
      (b \ a).card = n → MinimalStrongChain d a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a hab hn
        by_cases heq : a = b
        · subst a
          exact MinimalStrongChain.refl b
        · obtain ⟨c, hStep, hcStrong⟩ :=
            d.exists_minimalStrongStep_of_strong hab heq
          have hac : a ⊆ c := hStep.1.1
          have hcB : c ⊆ b := hcStrong.1
          have hStrict : a ≠ c := hStep.2.1
          have hNonempty : (c \ a).Nonempty := by
            by_contra hEmpty
            have hca : c ⊆ a := by
              intro x hx
              by_contra hxa
              exact hEmpty
                ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxa⟩⟩
            exact hStrict (le_antisymm hac hca)
          obtain ⟨v, hv⟩ := hNonempty
          have hVa : v ∉ a := (Finset.mem_sdiff.mp hv).2
          have hVc : v ∈ c := (Finset.mem_sdiff.mp hv).1
          have hVb : v ∈ b := hcB hVc
          have hSub : b \ c ⊆ b \ a := by
            intro x hx
            obtain ⟨hxb, hxc⟩ := Finset.mem_sdiff.mp hx
            exact Finset.mem_sdiff.mpr
              ⟨hxb, fun hxa => hxc (hac hxa)⟩
          have hNe : b \ c ≠ b \ a := by
            intro heqDiff
            have hva : v ∈ b \ a :=
              Finset.mem_sdiff.mpr ⟨hVb, hVa⟩
            have hvc : v ∉ b \ c := by
              intro h
              exact (Finset.mem_sdiff.mp h).2 hVc
            exact hvc (heqDiff ▸ hva)
          have hProper : b \ c ⊂ b \ a :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩
          have hLess : (b \ c).card < n := by
            have h := Finset.card_lt_card hProper
            rw [hn] at h
            exact h
          have hTail : MinimalStrongChain d c b :=
            ih (b \ c).card hLess c hcStrong rfl
          exact MinimalStrongChain.step hStep hTail
  exact core (b \ a).card a hab rfl

end Predimension
end BigHrushovski
