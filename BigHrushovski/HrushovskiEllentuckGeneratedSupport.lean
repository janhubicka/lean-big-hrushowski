import BigHrushovski.HrushovskiEllentuckSupport
import BigHrushovski.HrushovskiEllentuckSplicing

/-!
# Complete generated closures and finite level supports

For an ordered functional Hrushovski presentation, the finite support
of v is the set of levels represented in its *entire* generated closure.

This lemma package derives, rather than postulates, the compatibility
of finite supports with closure, the membership of v's own level in its
support, and the singleton-level witnesses used to recover level sets
from complete-support copy domains.

The package is general in a finite reflexive/transitive closure map Γ.
It does not claim that the actual C_F lift ranges equal these domains;
that requires finite unique lifting and the countable level action.
-/

namespace BigHrushovski.Ellentuck

universe u v
variable {Vertex : Type u} {Level : Type v}

/-- The complete finite set of levels represented in Γ(x). -/
noncomputable def generatedSupport
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (x : Vertex) : Finset Level := by
  classical
  exact (Γ x).image π

theorem mem_generatedSupport
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (x : Vertex) (q : Level) :
    q ∈ generatedSupport Γ π x ↔
      ∃ y, y ∈ Γ x ∧ π y = q := by
  classical
  simp [generatedSupport, Finset.mem_image]

/-- Reflexivity forces every vertex to represent its own level. -/
theorem own_level_mem_generatedSupport
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (hrefl : ∀ x, x ∈ Γ x) (x : Vertex) :
    π x ∈ generatedSupport Γ π x :=
  (mem_generatedSupport Γ π x (π x)).2 ⟨x, hrefl x, rfl⟩

/-- Transitivity of the *full* generated closure implies monotonicity
of the exact level support along any functional dependency. -/
theorem generatedSupport_subset_of_closure
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (htrans : ∀ {x y : Vertex}, y ∈ Γ x → Γ y ⊆ Γ x)
    {x y : Vertex} (hxy : y ∈ Γ x) :
    generatedSupport Γ π y ⊆ generatedSupport Γ π x := by
  intro q hq
  rcases (mem_generatedSupport Γ π y q).1 hq with ⟨z, hz, heq⟩
  exact (mem_generatedSupport Γ π x q).2
    ⟨z, htrans hxy hz, heq⟩

/-- Supported ranges are closed under all complete functional
dependencies, with no additional abstract support-transport axiom. -/
theorem generatedSupport_domain_closed
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (htrans : ∀ {x y : Vertex}, y ∈ Γ x → Γ y ⊆ Γ x)
    (S : Set Level) :
    IsUnaryClosed (fun x => (↑(Γ x) : Set Vertex))
      (supportDomain (generatedSupport Γ π) S) := by
  have hdep :
      ∀ {x y : Vertex}, y ∈ Γ x →
        generatedSupport Γ π y ⊆ generatedSupport Γ π x := by
    intro x y hxy
    exact generatedSupport_subset_of_closure Γ π htrans hxy
  intro x hx y hy
  exact supportDomain_closedUnder (generatedSupport Γ π)
    (fun a b => b ∈ Γ a) hdep hx hy

/-- With reflexivity, there can be no vertex with empty level support. -/
theorem generatedSupport_nonempty
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (hrefl : ∀ x, x ∈ Γ x) (x : Vertex) :
    (generatedSupport Γ π x).Nonempty :=
  ⟨π x, own_level_mem_generatedSupport Γ π hrefl x⟩

/-- The saturated copy domain over no levels is empty in any reflexive
finite generated-closure presentation. -/
theorem generatedSupport_empty_domain
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (hrefl : ∀ x, x ∈ Γ x) :
    supportDomain (generatedSupport Γ π) (∅ : Set Level) = ∅ :=
  supportDomain_empty_of_nonempty (generatedSupport Γ π)
    (generatedSupport_nonempty Γ π hrefl)

/-- Empty-support singleton blocks represent exact singleton level
supports, not merely an inclusion in the corresponding level fibre. -/
theorem generatedSupport_singleton
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    {q : Level} {z : Vertex}
    (hΓ : Γ z = {z}) (hπ : π z = q) :
    generatedSupport Γ π z = {q} := by
  classical
  simp [generatedSupport, hΓ, hπ]

/-- Complete singleton block witnesses recover inclusion of level sets
from inclusion of support-saturated vertex domains. -/
theorem generatedSupport_domain_subset_iff
    (Γ : Vertex → Finset Vertex) (π : Vertex → Level)
    (z : Level → Vertex)
    (hΓ : ∀ q, Γ (z q) = {z q})
    (hπ : ∀ q, π (z q) = q)
    (S T : Set Level) :
    supportDomain (generatedSupport Γ π) S ⊆
      supportDomain (generatedSupport Γ π) T ↔ S ⊆ T := by
  classical
  have hsingleton :
      ∀ q, generatedSupport Γ π (z q) = {q} := by
    intro q
    exact generatedSupport_singleton Γ π (hΓ q) (hπ q)
  exact supportDomain_subset_iff
    (generatedSupport Γ π) z hsingleton S T

end BigHrushovski.Ellentuck
