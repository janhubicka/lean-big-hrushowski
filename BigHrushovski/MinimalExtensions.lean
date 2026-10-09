import BigHrushovski.GlobalClosure

/-!
# Minimal closure increments

The next vertex is selected from a finite strong requirement. Its generated
closure over the current closed prefix is inclusion-minimal among candidates.
We show that every vertex in the increment generates the same relative
closure, and that there is no intermediate strong substructure.

The selection hypothesis is explicit in this module; the existence of a
minimising vertex is treated separately.
-/

namespace BigHrushovski
namespace Predimension
namespace StrongExhaustion

variable {V : Type*} [DecidableEq V] {d : Predimension V}
variable (e : StrongExhaustion d)

/-- Inclusion-minimality of the one-vertex closures among elements of D\a.
The condition only rules out proper subclosures of the chosen closure. -/
def IsMinimalChoice (a D : Finset V) (v : V) : Prop :=
  v ∈ D ∧ v ∉ a ∧
    ∀ x ∈ D, x ∉ a →
      e.closure (insert x a) ⊆ e.closure (insert v a) →
      e.closure (insert v a) ⊆ e.closure (insert x a)

/-- Every vertex of a minimal increment has the same relative closure. -/
theorem equal_closure_of_minimal_choice
    {a D : Finset V} {v : V}
    (hD : d.IsGloballyStrong D) (haD : a ⊆ D)
    (hchoice : e.IsMinimalChoice a D v)
    {x : V} (hx : x ∈ e.closure (insert v a)) (hxna : x ∉ a) :
    e.closure (insert x a) = e.closure (insert v a) := by
  have hgenD : insert v a ⊆ D := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwa
    · exact hchoice.1
    · exact haD hwa
  have hBD : e.closure (insert v a) ⊆ D :=
    e.closure_least_global (insert v a) D hD hgenD
  have hgenB : insert x a ⊆ e.closure (insert v a) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwa
    · exact hx
    · exact e.subset_closure (insert v a) (Finset.mem_insert_of_mem hwa)
  have hsubset : e.closure (insert x a) ⊆ e.closure (insert v a) :=
    e.closure_least_global (insert x a) (e.closure (insert v a))
      (e.closure_global (insert v a)) hgenB
  have hback : e.closure (insert v a) ⊆ e.closure (insert x a) :=
    hchoice.2.2 x (hBD hx) hxna hsubset
  exact le_antisymm hsubset hback

/-- The increment gives a minimal strong extension of the closed prefix.
There is no proper intermediate strong structure between the old prefix
and the generated hull. -/
theorem minimal_extension_of_choice
    {a D : Finset V} {v : V}
    (ha : d.IsGloballyStrong a)
    (hD : d.IsGloballyStrong D) (haD : a ⊆ D)
    (hchoice : e.IsMinimalChoice a D v) :
    d.IsStrong a (e.closure (insert v a)) ∧
    a ≠ e.closure (insert v a) ∧
    ∀ z : Finset V, a ⊆ z →
      z ⊆ e.closure (insert v a) →
      d.IsStrong z (e.closure (insert v a)) →
      z = a ∨ z = e.closure (insert v a) := by
  have haB : a ⊆ e.closure (insert v a) := by
    intro x hx
    exact e.subset_closure (insert v a) (Finset.mem_insert_of_mem hx)
  constructor
  · exact ha (e.closure (insert v a)) haB
  constructor
  · intro hEq
    have hvB : v ∈ e.closure (insert v a) :=
      e.subset_closure (insert v a) (Finset.mem_insert_self v a)
    rw [← hEq] at hvB
    exact hchoice.2.1 hvB
  · intro z haz hzB hzStrong
    by_cases hza : z = a
    · exact Or.inl hza
    · right
      have hExists : ∃ x : V, x ∈ z ∧ x ∉ a := by
        by_contra hne
        have hza' : z ⊆ a := by
          intro x hx
          by_contra hxna
          exact hne ⟨x, hx, hxna⟩
        exact hza (le_antisymm hza' haz)
      obtain ⟨x, hxz, hxna⟩ := hExists
      have hxB : x ∈ e.closure (insert v a) := hzB hxz
      have hEqCl : e.closure (insert x a) = e.closure (insert v a) :=
        e.equal_closure_of_minimal_choice hD haD hchoice hxB hxna
      have hzGlobal : d.IsGloballyStrong z :=
        d.globallyStrong_of_strong_in_global hzStrong (e.closure_global (insert v a))
      have hGenZ : insert x a ⊆ z := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hwa
        · exact hxz
        · exact haz hwa
      have hClZ : e.closure (insert x a) ⊆ z :=
        e.closure_least_global (insert x a) z hzGlobal hGenZ
      have hBZ : e.closure (insert v a) ⊆ z := by
        rw [← hEqCl]
        exact hClZ
      exact le_antisymm hzB hBZ

end StrongExhaustion
end Predimension
end BigHrushovski
