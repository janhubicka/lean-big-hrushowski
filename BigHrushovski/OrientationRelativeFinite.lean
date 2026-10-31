import BigHrushovski.InfiniteGraph
import Mathlib.Tactic

/-!
# A finite orientation interface for the relative orientation classes

An arrow is stored at its tail.  The outgoing-neighbour set is complete:
its image is not merely a positive-edge-preserving relation.  The source
class has at most two outgoing neighbours and no loops or opposite arrows.

This module proves only finite orientation facts used in Sections 7 and 8
of The Big Hrushovski.  It does not establish the successor-closure
Fraisse limit, recurrence, exact big Ramsey degrees, or the N_F sink
Rado obstruction.
-/

namespace BigHrushovski

structure FiniteOrientation (V : Type*) [DecidableEq V] where
  out : V → Finset V
  noLoop : ∀ x, x ∉ out x
  noOpposite : ∀ x y, y ∈ out x → x ∉ out y
  outDegreeTwo : ∀ x, (out x).card ≤ 2

namespace FiniteOrientation

variable {V : Type*} [DecidableEq V] (O : FiniteOrientation V)

def IsSink (x : V) : Prop := O.out x = ∅

def IsSuccessorClosed (s : Finset V) : Prop :=
  ∀ x ∈ s, O.out x ⊆ s

def Adjacent (x y : V) : Prop :=
  y ∈ O.out x ∨ x ∈ O.out y

/-- The undirected graph represented by complete outgoing-neighbour sets. -/
def underlying : GraphOn V where
  adj := O.Adjacent
  symm := by
    intro x y h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  irrefl := by
    intro x h
    rcases h with h | h
    · exact O.noLoop x h
    · exact O.noLoop x h

theorem successorClosed_empty : O.IsSuccessorClosed ∅ := by
  intro x hx
  simp at hx

theorem successorClosed_union {s t : Finset V}
    (hs : O.IsSuccessorClosed s)
    (ht : O.IsSuccessorClosed t) :
    O.IsSuccessorClosed (s ∪ t) := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hxS | hxT
  · exact Finset.mem_union_left t (hs x hxS hy)
  · exact Finset.mem_union_right s (ht x hxT hy)

theorem successorClosed_inter {s t : Finset V}
    (hs : O.IsSuccessorClosed s)
    (ht : O.IsSuccessorClosed t) :
    O.IsSuccessorClosed (s ∩ t) := by
  intro x hx y hy
  obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr ⟨hs x hxS hy, ht x hxT hy⟩

theorem singleton_successorClosed_of_sink {a : V}
    (ha : O.IsSink a) :
    O.IsSuccessorClosed {a} := by
  intro x hx y hy
  have hxa : x = a := Finset.mem_singleton.mp hx
  subst x
  rw [ha] at hy
  simp at hy

theorem pair_successorClosed_of_sinks {a b : V}
    (ha : O.IsSink a) (hb : O.IsSink b) :
    O.IsSuccessorClosed ({a, b} : Finset V) := by
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with hxa | hxb
  · subst x
    rw [ha] at hy
    simp at hy
  · have hxb' : x = b := Finset.mem_singleton.mp hxb
    subst x
    rw [hb] at hy
    simp at hy

/-- Distinct sinks cannot be joined by an oriented edge. -/
theorem sinks_nonadjacent {a b : V}
    (ha : O.IsSink a) (hb : O.IsSink b) :
    ¬ O.Adjacent a b := by
  intro h
  rcases h with h | h
  · rw [ha] at h
    simp at h
  · rw [hb] at h
    simp at h

/-- Two distinct outgoing neighbours exhaust the permitted out-degree. -/
theorem two_successors_outDegree {x a b : V}
    (hab : a ≠ b) (hxa : a ∈ O.out x) (hxb : b ∈ O.out x) :
    (O.out x).card = 2 := by
  have hsub : ({a, b} : Finset V) ⊆ O.out x := by
    intro y hy
    rcases Finset.mem_insert.mp hy with hya | hyb
    · subst y
      exact hxa
    · have hyb' : y = b := Finset.mem_singleton.mp hyb
      subst y
      exact hxb
  have hpair : ({a, b} : Finset V).card = 2 := by
    simp [hab]
  have hLower : 2 ≤ (O.out x).card := by
    simpa [hpair] using Finset.card_le_card hsub
  exact Nat.le_antisymm (O.outDegreeTwo x) hLower

/-- A structural form of the absence of four-cycles in the reduct.
It excludes four distinct vertices spanning a 4-cycle, whether induced or not. -/
def NoFourCycles : Prop :=
  ∀ a b x y : V,
    a ≠ b → x ≠ y →
    x ≠ a → x ≠ b → y ≠ a → y ≠ b →
    O.Adjacent x a → O.Adjacent x b →
    O.Adjacent y a → O.Adjacent y b → False

/-- In a four-cycle-free orientation two sinks have at most one
common predecessor pointing to both of them.  This is the
finite uniqueness input of the N_F sink-pair lemma. -/
theorem commonPredecessor_unique
    (hFour : O.NoFourCycles)
    {a b x y : V} (hab : a ≠ b)
    (hxa : a ∈ O.out x) (hxb : b ∈ O.out x)
    (hya : a ∈ O.out y) (hyb : b ∈ O.out y) :
    x = y := by
  by_contra hxy
  have hxaNe : x ≠ a := by
    intro h
    subst x
    exact O.noLoop a hxa
  have hxbNe : x ≠ b := by
    intro h
    subst x
    exact O.noLoop b hxb
  have hyaNe : y ≠ a := by
    intro h
    subst y
    exact O.noLoop a hya
  have hybNe : y ≠ b := by
    intro h
    subst y
    exact O.noLoop b hyb
  exact hFour a b x y hab hxy
    hxaNe hxbNe hyaNe hybNe
    (Or.inl hxa) (Or.inl hxb) (Or.inl hya) (Or.inl hyb)

end FiniteOrientation
end BigHrushovski
