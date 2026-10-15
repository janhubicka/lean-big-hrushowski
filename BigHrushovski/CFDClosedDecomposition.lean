import BigHrushovski.CFMinimalDClosed

/-!
# Absolute finite decomposition into minimal strict d-closed steps

This is the strict d-closed analogue of C0FiniteStrongFactorization.
For a finite d-closed inclusion a ≤d b, choose a proper d-closed
intermediate c of smallest cardinality. Strict d-closure restricts to
a ≤d c; if a ≤d z ≤d c then transitivity gives z ≤d b, contradicting
minimal cardinality unless z=a or z=c. Iteration decreases |b \ a|.

No ambient strong exhaustion, generic graph, or uniform bound is used.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)


/-- Every vertex set is d-closed in itself. -/
theorem dclosed_refl (a : Finset V) : d.IsDClosed a a := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro x hax hNe hxa
  exact (hNe (le_antisymm hxa hax)).elim

/-- Strict d-closedness restricts to any intermediate finite set. -/
theorem dclosed_restrict {a b c : Finset V}
    (hac : d.IsDClosed a c) (hab : a ⊆ b) (hbc : b ⊆ c) :
    d.IsDClosed a b := by
  refine ⟨hab, ?_⟩
  intro x hax hNe hxb
  exact hac.2 x hax hNe (hxb.trans hbc)

/-- A finite chain of minimal strict d-closed steps. -/
inductive MinimalDClosedChain (d : Predimension V) :
    Finset V → Finset V → Prop where
  | refl (a : Finset V) : MinimalDClosedChain d a a
  | step {a b c : Finset V}
      (hab : d.IsMinimalDClosedStep a b)
      (hbc : MinimalDClosedChain d b c) :
      MinimalDClosedChain d a c

/-- Every proper finite d-closed extension A ≤ B has a first
minimal d-closed step A < C with C ≤ B. -/
theorem exists_minimalDClosedStep_of_dClosed
    {a b : Finset V}
    (hab : d.IsDClosed a b) (hne : a ≠ b) :
    ∃ c : Finset V,
      d.IsMinimalDClosedStep a c ∧ d.IsDClosed c b := by
  classical
  let candidates : Finset (Finset V) :=
    b.powerset.filter (fun c => a ⊂ c ∧ d.IsDClosed c b)
  have hProper : a ⊂ b :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hab.1, hne⟩
  have hBCand : b ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl, hProper, d.dclosed_refl b⟩
  let sizes : Finset ℕ := candidates.image Finset.card
  have hSizes : sizes.Nonempty := by
    exact ⟨b.card, Finset.mem_image.mpr ⟨b, hBCand, rfl⟩⟩
  have hMinMem : sizes.min' hSizes ∈ sizes :=
    Finset.min'_mem sizes hSizes
  obtain ⟨c, hcCand, hcEq⟩ := Finset.mem_image.mp hMinMem
  obtain ⟨hcB, hAc, hcClosed⟩ :
      c ⊆ b ∧ a ⊂ c ∧ d.IsDClosed c b := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_powerset]
      using hcCand
  have hac : a ⊆ c :=
    (Finset.ssubset_iff_subset_ne.mp hAc).1
  have hacNe : a ≠ c :=
    (Finset.ssubset_iff_subset_ne.mp hAc).2
  have hacClosed : d.IsDClosed a c :=
    d.dclosed_restrict hab hac hcB
  have hMinimal : d.IsMinimalDClosedStep a c := by
    refine ⟨hacClosed, hacNe, ?_⟩
    intro z haz hzc hzClosed
    by_cases hEqA : z = a
    · exact Or.inl hEqA
    · right
      have hAZ : a ⊂ z :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨haz, by intro heq; exact hEqA heq.symm⟩
      have hzClosedB : d.IsDClosed z b :=
        d.dclosed_trans hzClosed hcClosed
      have hzCand : z ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hzc.trans hcB, hAZ, hzClosedB⟩
      have hzSize : z.card ∈ sizes :=
        Finset.mem_image.mpr ⟨z, hzCand, rfl⟩
      have hCard : c.card ≤ z.card := by
        rw [hcEq]
        exact Finset.min'_le sizes z.card hzSize
      exact Finset.eq_of_subset_of_card_le hzc hCard
  exact ⟨c, hMinimal, hcClosed⟩

/-- Every finite d-closed inclusion A ≤ B admits a finite chain of
minimal d-closed steps. No ambient strong-exhaustion hypothesis is used. -/
theorem finite_minimal_decomposition_of_dClosed_absolute
    {a b : Finset V}
    (hab : d.IsDClosed a b) :
    MinimalDClosedChain d a b := by
  classical
  have core : ∀ n : ℕ, ∀ a : Finset V,
      d.IsDClosed a b →
      (b \ a).card = n → MinimalDClosedChain d a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a hab hn
        by_cases heq : a = b
        · subst a
          exact MinimalDClosedChain.refl b
        · obtain ⟨c, hStep, hcClosed⟩ :=
            d.exists_minimalDClosedStep_of_dClosed hab heq
          have hac : a ⊆ c := hStep.1.1
          have hcB : c ⊆ b := hcClosed.1
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
          have hTail : MinimalDClosedChain d c b :=
            ih (b \ c).card hLess c hcClosed rfl
          exact MinimalDClosedChain.step hStep hTail
  exact core (b \ a).card a hab rfl

end Predimension
end BigHrushovski
