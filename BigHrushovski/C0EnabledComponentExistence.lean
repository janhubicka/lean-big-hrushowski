import BigHrushovski.C0EnabledComponentStep

/-!
# Countable C₀: existence of an enabled intrinsic component

For any finite Q, choose an unlisted vertex of least finite
complete-closure cardinality. Every strict lower dependency of this
vertex must already lie in Q. Thus an enabled component always exists,
without requiring Q to be closed.

If Q is closed and the ambient graph has cofinal exact canonical
C₀ stages, the enabled-component theorem supplies an actual minimal
strong extension and a globally strong new finite prefix.

This is an existence-of-next-step result, not a fair enumeration.
-/

namespace BigHrushovski
namespace FiniteC0

/-- For every finite subset Q of an infinite carrier ℕ with complete
finite-valued unary closure C, there is a vertex outside Q whose
entire strict lower dependency set is contained in Q.

Proof: minimize the finite cardinality |C x| among vertices outside
Q, rather than attempting to sort *all* components globally by rank. -/
theorem exists_enabledVertex
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) :
    ∃ x : ℕ, x ∉ Q ∧ strictLowerValue C x ⊆ Q := by
  classical
  have hOutside : ∃ x : ℕ, x ∉ Q := by
    refine ⟨Q.sup id + 1, ?_⟩
    intro hx
    have hBound : Q.sup id + 1 ≤ Q.sup id := Finset.le_sup hx
    omega
  let p : ℕ → Prop :=
    fun k => ∃ x : ℕ, x ∉ Q ∧ (C x).card = k
  have hp : ∃ k : ℕ, p k := by
    obtain ⟨x, hx⟩ := hOutside
    exact ⟨(C x).card, x, hx, rfl⟩
  let k : ℕ := Nat.find hp
  have hk : p k := Nat.find_spec hp
  obtain ⟨x, hx, hCard⟩ := hk
  refine ⟨x, hx, ?_⟩
  intro y hy
  by_contra hyQ
  have hlt : (C y).card < (C x).card :=
    strictLowerValue_card_lt C hC hy
  have hltK : (C y).card < k := by
    calc
      (C y).card < (C x).card := hlt
      _ = k := hCard
  have hMin : ¬ p (C y).card := Nat.find_min hp hltK
  exact hMin ⟨y, hyQ, rfl⟩

/-- Among enabled vertices, choose the least natural label.
This is the fair priority rule used by the prospective component
enumeration. It does not assert that the resulting recursion has been
constructed or that every component is eventually selected. -/
theorem exists_least_enabledVertex
    (C : ℕ → Finset ℕ) (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) :
    ∃ x : ℕ,
      (x ∉ Q ∧ strictLowerValue C x ⊆ Q) ∧
      (∀ y : ℕ, (y ∉ Q ∧ strictLowerValue C y ⊆ Q) → x ≤ y) := by
  let p : ℕ → Prop :=
    fun x => x ∉ Q ∧ strictLowerValue C x ⊆ Q
  have hp : ∃ x : ℕ, p x :=
    exists_enabledVertex C hC Q
  refine ⟨Nat.find hp, Nat.find_spec hp, ?_⟩
  intro y hy
  exact Nat.find_min' hp hy

/-- A finite C-closed set in a countable canonical C₀ graph always
has a strictly larger finite globally strong extension which is one
minimal strong component step. The witness is an actual vertex x
of the original graph, not an abstract component quotient. -/
theorem canonicalStages_exists_enabledStep
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q) :
    ∃ x : ℕ, x ∉ Q ∧
      N.toPredimension.IsMinimalStrongStep
        Q (Q ∪ unaryComponent C x) ∧
      N.toPredimension.IsGloballyStrong
        (Q ∪ unaryComponent C x) := by
  have hC : IsCompleteUnaryClosure C :=
    completeUnary_of_canonicalFiniteStages N C stage hCover hStage
  obtain ⟨x, hxNotQ, hLower⟩ :=
    exists_enabledVertex C hC Q
  refine ⟨x, hxNotQ, ?_⟩
  exact canonicalStages_enabledComponent_step_and_strong
    N C stage hCover hStage Q hClosedQ x hxNotQ hLower

end FiniteC0
end BigHrushovski
