import Mathlib.Tactic

/-!
# Counting finite choices with prior-dependent fibres

At each stage the permitted next choices can depend on the complete
history of earlier choices. If the number of choices at stage n is
uniformly g(n), independently of that history, then the number of
resulting complete histories is the product of the g(n).

This elementary lemma isolates the counting step needed when an
N₀ component's permitted internal orders depend on the already
ordered lower successor part. Independence of the *sets* of
choices is unnecessary. It does not construct an N₀ order or prove
a big Ramsey theorem.
-/

namespace BigHrushovski
namespace FiniteChoiceHistory

variable {α : Type*} [DecidableEq α]

/-- Length-n histories of permitted choices. The prior is stored
in reverse order (most recent choice first), while the resulting
history lists choices in their chronological order. -/
noncomputable def histories (choose : ℕ → List α → Finset α) :
    (n : ℕ) → List α → Finset (List α)
  | 0, _ => {[]}
  | n + 1, prior =>
      (choose n prior).biUnion (fun a =>
        (histories choose n (a :: prior)).image (List.cons a))

/-- Every resulting suffix has precisely the prescribed number
of steps, even when some choice sets are empty. -/
theorem length_of_mem_histories
    (choose : ℕ → List α → Finset α) :
    ∀ (n : ℕ) (prior history : List α),
      history ∈ histories choose n prior → history.length = n := by
  intro n
  induction n with
  | zero =>
      intro prior history h
      have hnil : history = [] := by
        simpa [histories] using h
      subst history
      rfl
  | succ n ih =>
      intro prior history h
      change history ∈
        (choose n prior).biUnion (fun a =>
          (histories choose n (a :: prior)).image (List.cons a)) at h
      obtain ⟨a, ha, hImage⟩ := Finset.mem_biUnion.mp h
      obtain ⟨tail, htail, hEq⟩ := Finset.mem_image.mp hImage
      subst history
      simpa using congrArg Nat.succ (ih (a :: prior) tail htail)

/-- The sets of histories beginning with distinct next choices
are disjoint, even though the remaining choices depend on the
chosen first element. -/
theorem history_first_choice_disjoint
    (choose : ℕ → List α → Finset α)
    (n : ℕ) (prior : List α) :
    ((choose n prior : Finset α) : Set α).PairwiseDisjoint
      (fun a => (histories choose n (a :: prior)).image
        (List.cons a)) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro l hl hr
  obtain ⟨u, hu, hEqU⟩ := Finset.mem_image.mp hl
  obtain ⟨v, hv, hEqV⟩ := Finset.mem_image.mp hr
  have hCons : a :: u = b :: v := hEqU.trans hEqV.symm
  have hHead : a = b := by
    have h := congrArg List.head? hCons
    simpa using h
  exact hab hHead

/-- Uniform fibre cardinalities imply the exact product formula
for dependent finite histories. The choice *sets* may be entirely
different for different previous histories. -/
theorem histories_card
    (choose : ℕ → List α → Finset α) (g : ℕ → ℕ)
    (hUniform : ∀ (n : ℕ) (prior : List α),
      (choose n prior).card = g n) :
    ∀ (n : ℕ) (prior : List α),
      (histories choose n prior).card =
        ∏ i ∈ Finset.range n, g i := by
  intro n
  induction n with
  | zero =>
      intro prior
      simp [histories]
  | succ n ih =>
      intro prior
      change ((choose n prior).biUnion (fun a =>
        (histories choose n (a :: prior)).image (List.cons a))).card =
        ∏ i ∈ Finset.range (n + 1), g i
      calc
        _ = ∑ a ∈ choose n prior,
              ((histories choose n (a :: prior)).image
                (List.cons a)).card :=
          Finset.card_biUnion
            (history_first_choice_disjoint choose n prior)
        _ = ∑ a ∈ choose n prior,
              (histories choose n (a :: prior)).card := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.card_image_iff.mpr
          intro u hu v hv huv
          have hTail := congrArg List.tail huv
          simpa using hTail
        _ = ∑ a ∈ choose n prior,
              ∏ i ∈ Finset.range n, g i := by
          apply Finset.sum_congr rfl
          intro a ha
          exact ih (a :: prior)
        _ = (choose n prior).card *
              (∏ i ∈ Finset.range n, g i) := by
          simp
        _ = ∏ i ∈ Finset.range (n + 1), g i := by
          rw [hUniform n prior, Finset.prod_range_succ]
          exact Nat.mul_comm _ _

end FiniteChoiceHistory
end BigHrushovski
