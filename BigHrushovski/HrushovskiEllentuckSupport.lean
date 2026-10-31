import Mathlib

/-!
# Finite-support ranges for Hrushovski level spaces

For the C_F rational and omega-level presentations the domain of a lifted
copy is not the union of whole level fibres. A vertex is retained precisely
when *every* level of its complete functional closure is retained.

This file proves the common finite-support calculus without presupposing
the unique level-lifting theorem. It does not assert that the represented
domains are all functional self-copies: that requires Track B.
-/

namespace BigHrushovski.Ellentuck

universe u v

variable {Level : Type u} {Vertex : Type v}
variable (support : Vertex → Finset Level)

/-- Vertices whose complete finite level support is contained in S. -/
def supportDomain (S : Set Level) : Set Vertex :=
  {x | ∀ q ∈ support x, q ∈ S}

theorem mem_supportDomain {S : Set Level} {x : Vertex} :
    x ∈ supportDomain support S ↔ ∀ q ∈ support x, q ∈ S :=
  Iff.rfl

/-- Retaining more levels cannot remove any fully supported vertex. -/
theorem supportDomain_mono {S T : Set Level} (hST : S ⊆ T) :
    supportDomain support S ⊆ supportDomain support T := by
  intro x hx q hq
  exact hST (hx q hq)

/-- Membership of a given vertex depends on finitely many level
coordinates, namely the elements of its complete support. -/
theorem supportDomain_local (S T : Set Level) (v : Vertex)
    (hST : ∀ q ∈ support v, (q ∈ S ↔ q ∈ T)) :
    v ∈ supportDomain support S ↔ v ∈ supportDomain support T := by
  constructor
  · intro hv q hq
    exact (hST q hq).mp (hv q hq)
  · intro hv q hq
    exact (hST q hq).mpr (hv q hq)

/-- A single missing closure-support level excludes the vertex. A
vertex's own level being retained does not suffice. -/
theorem supportDomain_excludes_missing
    {S : Set Level} {v : Vertex} {q : Level}
    (hq : q ∈ support v) (hnot : q ∉ S) :
    v ∉ supportDomain support S := by
  intro hv
  exact hnot (hv q hq)

/-- Every vertex in a saturated range already belongs to a finite-level
subrange. This is the set-theoretic part of the displayed union
M[S] = ⋃{M[T] : T ⊆ S finite} in the manuscript. -/
theorem mem_supportDomain_iff_finite_witness
    (S : Set Level) (v : Vertex) :
    v ∈ supportDomain support S ↔
      ∃ T : Finset Level, (↑T : Set Level) ⊆ S ∧
        v ∈ supportDomain support (↑T : Set Level) := by
  constructor
  · intro hv
    refine ⟨support v, ?_, ?_⟩
    · intro q hq
      exact hv q hq
    · intro q hq
      exact hq
  · rintro ⟨T, hTS, hv⟩
    exact supportDomain_mono support hTS hv

/-- Exact preservation of intersections, unlike unions. -/
theorem supportDomain_inter (S T : Set Level) :
    supportDomain support (S ∩ T) =
      supportDomain support S ∩ supportDomain support T := by
  ext x
  constructor
  · intro hx
    exact ⟨fun q hq => (hx q hq).1,
           fun q hq => (hx q hq).2⟩
  · rintro ⟨hxS, hxT⟩ q hq
    exact ⟨hxS q hq, hxT q hq⟩

theorem supportDomain_univ :
    supportDomain support (Set.univ : Set Level) = Set.univ := by
  ext x
  simp [supportDomain]

/-- In the concrete level presentations every vertex represents its own
level, hence has nonempty complete level support. In particular the
empty-level range is empty; this fails without that hypothesis. -/
theorem supportDomain_empty_of_nonempty
    (hnonempty : ∀ x : Vertex, (support x).Nonempty) :
    supportDomain support (∅ : Set Level) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases hnonempty x with ⟨q, hq⟩
    exact False.elim (hx q hq)
  · intro hx
    exact False.elim hx

/-- Empty-support vertices belong to every support-saturated domain. -/
theorem empty_support_mem (x : Vertex) (h : support x = ∅)
    (S : Set Level) : x ∈ supportDomain support S := by
  simp [supportDomain, h]

section SingletonWitness

variable [DecidableEq Level]
variable (singleton : Level → Vertex)
variable (hsingleton : ∀ q, support (singleton q) = {q})

/-- Singleton-support level vertices detect membership of levels. -/
theorem singleton_mem_supportDomain (S : Set Level) (q : Level) :
    singleton q ∈ supportDomain support S ↔ q ∈ S := by
  simp [supportDomain, hsingleton q]

/-- Inclusion of saturated domains reflects inclusion of level sets. -/
theorem supportDomain_subset_iff (S T : Set Level) :
    supportDomain support S ⊆ supportDomain support T ↔ S ⊆ T := by
  constructor
  · intro h q hq
    apply (singleton_mem_supportDomain support singleton hsingleton T q).1
    exact h ((singleton_mem_supportDomain support singleton hsingleton S q).2 hq)
  · exact supportDomain_mono support

/-- The complete-support range representation is injective. -/
theorem supportDomain_injective :
    Function.Injective (supportDomain support) := by
  intro S T h
  apply Set.Subset.antisymm
  · exact (supportDomain_subset_iff support singleton hsingleton S T).1
      (le_of_eq h)
  · exact (supportDomain_subset_iff support singleton hsingleton T S).1
      (le_of_eq h.symm)

end SingletonWitness

/-- A transitive dependency relation makes support-saturated ranges closed. -/
theorem supportDomain_closedUnder (depends : Vertex → Vertex → Prop)
    (hdep : ∀ {v w}, depends v w → support w ⊆ support v)
    {S : Set Level} {v w : Vertex}
    (hv : v ∈ supportDomain support S)
    (hvw : depends v w) :
    w ∈ supportDomain support S := by
  intro q hq
  exact hv q (hdep hvw hq)

end BigHrushovski.Ellentuck
