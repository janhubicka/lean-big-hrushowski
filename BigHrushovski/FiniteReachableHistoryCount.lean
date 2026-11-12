import BigHrushovski.FiniteDependentChoiceCount
import Mathlib.Tactic

/-!
# Counting finite histories with uniform reachable fibres

For the finite ordered expansion of N₀, the admissible choices for
a component depend on earlier component orders. A uniform counting
hypothesis should therefore be checked on histories that can actually
occur; it is unnecessary (and generally false) on arbitrary lists.

We record histories in reverse chronological order, with the most
recent choice at the head. At stage n, an admissible history of length
n extends by one of the choices attached to that history.

If each reachable stage-n history has exactly g(n) successors, then
the number of reachable length-n histories is the product of the
g(i). There is no assumption that the sets of successors coincide
for two different histories.

The lemma is purely finite combinatorics. It does not identify the
histories with permitted component orders; that remains a separate
finite geometric obligation.
-/

namespace BigHrushovski
namespace FiniteChoiceHistory

variable {α : Type*} [DecidableEq α]

/-- Reachable histories of length n, most recent choice first.
Only histories produced by the previous stages are extended. -/
noncomputable def reachableHistories
    (choose : List α → Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 =>
      (reachableHistories choose n).biUnion (fun prior =>
        (choose prior).image (fun a => a :: prior))

/-- Every reachable stage-n history contains exactly n choices. -/
theorem length_of_mem_reachableHistories
    (choose : List α → Finset α) :
    ∀ (n : ℕ) (history : List α),
      history ∈ reachableHistories choose n →
      history.length = n := by
  intro n
  induction n with
  | zero =>
      intro history h
      have hh : history = [] := by
        simpa [reachableHistories] using h
      subst history
      rfl
  | succ n ih =>
      intro history h
      change history ∈
        (reachableHistories choose n).biUnion
          (fun prior => (choose prior).image
            (fun a => a :: prior)) at h
      obtain ⟨prior, hprior, hImage⟩ := Finset.mem_biUnion.mp h
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hImage
      subst history
      simpa using congrArg Nat.succ (ih prior hprior)

/-- Extensions of distinct histories are disjoint, since removing
the first entry recovers the complete preceding history. -/
theorem reachableExtensions_pairwiseDisjoint
    (choose : List α → Finset α) (n : ℕ) :
    (((reachableHistories choose n) : Finset (List α)) :
      Set (List α)).PairwiseDisjoint
        (fun prior => (choose prior).image (fun a => a :: prior)) := by
  intro prior hprior other hother hne
  apply Finset.disjoint_left.mpr
  intro history hFirst hSecond
  obtain ⟨a, ha, hEqA⟩ := Finset.mem_image.mp hFirst
  obtain ⟨b, hb, hEqB⟩ := Finset.mem_image.mp hSecond
  have hCons : a :: prior = b :: other := hEqA.trans hEqB.symm
  have hPrior : prior = other := by
    have hTail := congrArg List.tail hCons
    simpa using hTail
  exact hne hPrior

/-- Exact dependent-fibre count, assuming uniform cardinalities
only for *reachable* histories. This is strictly weaker than
requiring uniformity for every arbitrary prior list. -/
theorem reachableHistories_card
    (choose : List α → Finset α) (g : ℕ → ℕ)
    (hUniform : ∀ (n : ℕ) (prior : List α),
      prior ∈ reachableHistories choose n →
      (choose prior).card = g n) :
    ∀ (n : ℕ),
      (reachableHistories choose n).card =
        ∏ i ∈ Finset.range n, g i := by
  intro n
  induction n with
  | zero =>
      simp [reachableHistories]
  | succ n ih =>
      change
        ((reachableHistories choose n).biUnion
          (fun prior => (choose prior).image
            (fun a => a :: prior))).card =
          ∏ i ∈ Finset.range (n + 1), g i
      calc
        _ = ∑ prior ∈ reachableHistories choose n,
              ((choose prior).image
                (fun a => a :: prior)).card :=
          Finset.card_biUnion
            (reachableExtensions_pairwiseDisjoint choose n)
        _ = ∑ prior ∈ reachableHistories choose n,
              (choose prior).card := by
          apply Finset.sum_congr rfl
          intro prior hprior
          apply Finset.card_image_iff.mpr
          intro a ha b hb hab
          have hHead := congrArg List.head? hab
          simpa using hHead
        _ = ∑ prior ∈ reachableHistories choose n, g n := by
          apply Finset.sum_congr rfl
          intro prior hprior
          exact hUniform n prior hprior
        _ = (reachableHistories choose n).card * g n := by simp
        _ = ∏ i ∈ Finset.range (n + 1), g i := by
          rw [ih, Finset.prod_range_succ]

end FiniteChoiceHistory
end BigHrushovski
