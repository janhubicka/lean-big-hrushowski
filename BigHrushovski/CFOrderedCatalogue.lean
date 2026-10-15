import BigHrushovski.CFLocalSupport
import BigHrushovski.FiniteCatalogue
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite catalogue of ordered local C_F extension types

A local type over an *actual named* finite base P is represented on
P ⊕ Fin n.  The old vertices retain their names and inherited order;
the new block is indexed by Fin n in its chosen order.  The code
stores the entire finite graph, not only its boundary edges.

Admissibility is an explicit predicate supplied by the intended
growth-function class. We do not infer class membership, free
amalgamation in C_F, or a uniform closure bound merely from
submodularity of graph predimension.

At each fixed fresh size n there are finitely many codes. If a
published uniform bound K applies to closures of the old base and
one fresh vertex, minimal d-closedness implies
  |P| + n ≤ K,
and hence only finitely many n and finitely many ordered types.
This is the finite catalogue input, not the countable level schedule.
-/

namespace BigHrushovski
namespace CFLocalCatalogue

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The names of the old support vertices on P ⊕ Fin n. -/
def oldVertices (P : Type*) [Fintype P] [DecidableEq P]
    (n : ℕ) : Finset (Sum P (Fin n)) :=
  (Finset.univ : Finset P).image (fun p => (Sum.inl p : Sum P (Fin n)))

/-- The fresh ordered block; its labels are Fin n in their natural order. -/
def freshVertices (P : Type*) [Fintype P] [DecidableEq P]
    (n : ℕ) : Finset (Sum P (Fin n)) :=
  (Finset.univ : Finset (Fin n)).image
    (fun i => (Sum.inr i : Sum P (Fin n)))

theorem old_fresh_disjoint (P : Type*) [Fintype P] [DecidableEq P]
    (n : ℕ) :
    Disjoint (oldVertices P n) (freshVertices P n) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hvOld hvFresh
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hvOld
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hvFresh
  rw [← hp] at hi
  cases hi

theorem old_union_fresh (P : Type*) [Fintype P] [DecidableEq P]
    (n : ℕ) :
    oldVertices P n ∪ freshVertices P n =
      (Finset.univ : Finset (Sum P (Fin n))) := by
  classical
  ext v
  cases v with
  | inl p => simp [oldVertices, freshVertices]
  | inr i => simp [oldVertices, freshVertices]

/-- A graph with n ordered new vertices, over the literally named
old base. A class-membership predicate is supplied rather than
assumed from the finite predimension calculations. -/
structure OrderedLocalType
    (P : Type*) [Fintype P] [DecidableEq P]
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (n : ℕ) where
  graph : GraphOn (Sum P (Fin n))
  base_agrees : ∀ p q : P,
    graph.adj (Sum.inl p) (Sum.inl q) ↔ base.adj p q
  allowed : Allowed n graph
  minimal : graph.toPredimension.IsMinimalDClosedStep
    (oldVertices P n) Finset.univ
  exact_support :
    graph.toPredimension.dClosedHull
      (graph.oldNeighbourSet (oldVertices P n) (freshVertices P n))
      (oldVertices P n) = oldVertices P n

/-- Every fixed-size local type is one of finitely many graph codes.
All the additional properties are propositions and introduce no
extra coding choices. -/
noncomputable instance finite_graphOn_sum (n : ℕ) :
    Finite (GraphOn (Sum P (Fin n))) := by
  classical
  have h : Function.Injective
      (fun G : GraphOn (Sum P (Fin n)) => G.adj) := by
    intro G H hEq
    cases G
    cases H
    cases hEq
    rfl
  exact Finite.of_injective (fun G : GraphOn (Sum P (Fin n)) => G.adj) h

noncomputable instance finite_orderedLocalType
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (n : ℕ) : Finite (OrderedLocalType P base Allowed n) := by
  classical
  have h : Function.Injective
      (fun t : OrderedLocalType P base Allowed n => t.graph) := by
    intro a b hEq
    cases a
    cases b
    cases hEq
    rfl
  exact Finite.of_injective
    (fun t : OrderedLocalType P base Allowed n => t.graph) h

/-- An ordered type of fresh size at most K, with its exact size
remembered in the dependent index. -/
abbrev BoundedOrderedLocalType
    (P : Type*) [Fintype P] [DecidableEq P]
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K : ℕ) :=
  Σ n : Fin (K + 1), OrderedLocalType P base Allowed n.val

noncomputable instance finite_boundedCatalogue
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K : ℕ) :
    Finite (BoundedOrderedLocalType P base Allowed K) := by
  classical
  letI : ∀ i : Fin (K + 1),
      Finite (OrderedLocalType P base Allowed i.val) :=
    fun i => finite_orderedLocalType base Allowed i.val
  infer_instance

/-- The whole finite collection of permitted ordered codes.
Empty is allowed when no local extension is admissible. -/
noncomputable def catalogue (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K : ℕ) : Finset (BoundedOrderedLocalType P base Allowed K) := by
  classical
  letI : Fintype (BoundedOrderedLocalType P base Allowed K) :=
    Fintype.ofFinite _
  exact Finset.univ

theorem mem_catalogue
    (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K : ℕ) (t : BoundedOrderedLocalType P base Allowed K) :
    t ∈ catalogue base Allowed K := by
  classical
  simp [catalogue]

/-- Include a fixed-size local code in the finite catalogue once
the closure bound has supplied n ≤ K. -/
def toBounded (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K n : ℕ) (hn : n ≤ K)
    (t : OrderedLocalType P base Allowed n) :
    BoundedOrderedLocalType P base Allowed K :=
  ⟨⟨n, Nat.lt_succ_of_le hn⟩, t⟩

theorem toBounded_mem (base : GraphOn P)
    (Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop)
    (K n : ℕ) (hn : n ≤ K)
    (t : OrderedLocalType P base Allowed n) :
    toBounded base Allowed K n hn t ∈ catalogue base Allowed K :=
  mem_catalogue base Allowed K _

/-- Minimal strict d-closedness forces the fresh block to be nonempty. -/
theorem OrderedLocalType.fresh_pos
    {base : GraphOn P}
    {Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop}
    {n : ℕ} (t : OrderedLocalType P base Allowed n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have hEq : oldVertices P 0 =
      (Finset.univ : Finset (Sum P (Fin 0))) := by
    classical
    ext v
    cases v with
    | inl p => simp [oldVertices]
    | inr i => exact Fin.elim0 i
  exact t.minimal.2.1 hEq

/-- If the generated closure of the old base with one fresh vertex
has at most K vertices, then the *whole* minimal extension has at
most K vertices. This uses the verified every-generator theorem. -/
theorem OrderedLocalType.total_size_le_of_generator_bound
    {base : GraphOn P}
    {Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop}
    {n : ℕ} (t : OrderedLocalType P base Allowed n)
    (K : ℕ) (x : Fin n)
    (hBound : (t.graph.toPredimension.dClosedHull
      (insert (Sum.inr x) (oldVertices P n))
      (Finset.univ : Finset (Sum P (Fin n)))).card ≤ K) :
    Fintype.card P + n ≤ K := by
  classical
  have hxNot : (Sum.inr x : Sum P (Fin n)) ∉ oldVertices P n := by
    simp [oldVertices]
  have hGen := t.graph.toPredimension.minimalDClosedStep_every_generator
    t.minimal (Finset.mem_univ _) hxNot
  rw [hGen] at hBound
  simpa only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
    using hBound

/-- Under a uniform one-generator bound, the fresh size lies in
the finite range used by the explicit catalogue. -/
theorem OrderedLocalType.fresh_size_le_of_uniform_bound
    {base : GraphOn P}
    {Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop}
    {n : ℕ} (t : OrderedLocalType P base Allowed n)
    (K : ℕ)
    (hBound : ∀ x : Fin n,
      (t.graph.toPredimension.dClosedHull
        (insert (Sum.inr x) (oldVertices P n))
        (Finset.univ : Finset (Sum P (Fin n)))).card ≤ K) :
    n ≤ K := by
  let x : Fin n := ⟨0, t.fresh_pos⟩
  have hTotal := t.total_size_le_of_generator_bound K x (hBound x)
  omega

/-- Every admissible local type satisfying the explicit uniform
closure bound occurs in the finite labelled catalogue. -/
theorem OrderedLocalType.occurs_of_uniform_bound
    {base : GraphOn P}
    {Allowed : ∀ n : ℕ, GraphOn (Sum P (Fin n)) → Prop}
    {n : ℕ} (t : OrderedLocalType P base Allowed n)
    (K : ℕ)
    (hBound : ∀ x : Fin n,
      (t.graph.toPredimension.dClosedHull
        (insert (Sum.inr x) (oldVertices P n))
        (Finset.univ : Finset (Sum P (Fin n)))).card ≤ K) :
    ∃ code : BoundedOrderedLocalType P base Allowed K,
      code.1.val = n ∧
        code ∈ catalogue base Allowed K := by
  let hn : n ≤ K := t.fresh_size_le_of_uniform_bound K hBound
  refine ⟨toBounded base Allowed K n hn t, rfl, ?_⟩
  exact toBounded_mem base Allowed K n hn t

end CFLocalCatalogue
end BigHrushovski
