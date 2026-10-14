import BigHrushovski.C0FiniteStrongFactorization

/-!
# Finite minimal strong chains as literal lists of fresh vertex blocks

A MinimalStrongChain is an inductively stated existence assertion
about strong intermediate vertex sets. To construct a finite
functional component indexing, we instead need an actual finite
list of *disjoint fresh blocks* B_0,...,B_(m-1), where each
A_(i+1)=A_i∪B_i is minimal strong and the final set is exactly
the prescribed finite strong extension.

This module converts both descriptions in both directions.
The transformation is entirely finite and does not assume a
strong exhaustion or a countable generic structure.

The resulting run is the input for iterating the certified
single-final-block C0 unary-function append theorem.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Attach a given finite list of new vertex blocks to a finite
old vertex set, retaining the whole current prefix at every step. -/
def blockRunEnd (a : Finset V) (blocks : List (Finset V)) : Finset V :=
  blocks.foldl (fun old B => old ∪ B) a

/-- The complete list of strong certificates: every new block is
disjoint from the current old part and makes precisely one
minimal strong extension of that old part. -/
def IsMinimalBlockRun (d : Predimension V) (a : Finset V) :
    List (Finset V) → Prop
  | [] => True
  | B :: rest =>
      Disjoint a B ∧
      d.IsMinimalStrongStep a (a ∪ B) ∧
      d.IsMinimalBlockRun (a ∪ B) rest

/-- A nontrivial minimal strong step A<B is given by the literal
fresh block B\A; its old and new vertices are disjoint and their
union is the whole target B. -/
theorem freshBlock_of_minimal
    (d : Predimension V)
    {a b : Finset V} (hab : d.IsMinimalStrongStep a b) :
    Disjoint a (b \ a) ∧ a ∪ (b \ a) = b := by
  have habSub : a ⊆ b := hab.1.1
  constructor
  · apply Finset.disjoint_left.mpr
    intro v ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  · ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with ha | hb
      · exact habSub ha
      · exact (Finset.mem_sdiff.mp hb).1
    · intro hv
      by_cases ha : v ∈ a
      · exact Finset.mem_union.mpr (Or.inl ha)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hv,ha⟩))

/-- Every finite minimal strong chain admits an explicit complete
list of non-overlapping fresh blocks, with no missing endpoint. -/
theorem MinimalStrongChain.exists_blockRun
    {d : Predimension V} {a b : Finset V}
    (h : MinimalStrongChain d a b) :
    ∃ blocks : List (Finset V),
      d.IsMinimalBlockRun a blocks ∧ blockRunEnd a blocks = b := by
  induction h with
  | refl a =>
      exact ⟨[], by trivial, rfl⟩
  | @step a b c hab hbc ih =>
      obtain ⟨blocks, hRun, hEnd⟩ := ih
      let B : Finset V := b \ a
      have hDisj : Disjoint a B := (freshBlock_of_minimal d hab).1
      have hUnion : a ∪ B = b := (freshBlock_of_minimal d hab).2
      refine ⟨B :: blocks, ?_, ?_⟩
      · change Disjoint a B ∧ d.IsMinimalStrongStep a (a ∪ B) ∧
          d.IsMinimalBlockRun (a ∪ B) blocks
        refine ⟨hDisj, ?_, ?_⟩
        · rw [hUnion]
          exact hab
        · rw [hUnion]
          exact hRun
      · change blockRunEnd (a ∪ B) blocks = c
        rw [hUnion]
        exact hEnd

/-- Conversely, a literal run of disjoint minimal strong fresh
blocks gives precisely an inductive chain of minimal strong steps. -/
theorem IsMinimalBlockRun.toChain
    (d : Predimension V) (a : Finset V)
    (blocks : List (Finset V))
    (h : d.IsMinimalBlockRun a blocks) :
    MinimalStrongChain d a (blockRunEnd a blocks) := by
  induction blocks generalizing a with
  | nil =>
      exact MinimalStrongChain.refl a
  | cons B rest ih =>
      change Disjoint a B ∧ d.IsMinimalStrongStep a (a ∪ B) ∧
        d.IsMinimalBlockRun (a ∪ B) rest at h
      rcases h with ⟨_,hStep,hRest⟩
      change MinimalStrongChain d a
        (blockRunEnd (a ∪ B) rest)
      exact MinimalStrongChain.step hStep
        (ih (a ∪ B) hRest)

/-- Every finite strong extension admits a literal finite list of
disjoint nonempty minimal strong blocks, without any ambient
strong-exhaustion hypothesis. -/
theorem exists_minimalBlockRun_of_strong
    (d : Predimension V) {a b : Finset V}
    (hab : d.IsStrong a b) :
    ∃ blocks : List (Finset V),
      d.IsMinimalBlockRun a blocks ∧ blockRunEnd a blocks = b :=
  (d.finite_minimal_decomposition_of_strong_absolute hab).exists_blockRun

end Predimension
end BigHrushovski
