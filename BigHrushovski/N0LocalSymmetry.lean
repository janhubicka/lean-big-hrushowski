import BigHrushovski.OrientationComponentDownsets
import Mathlib.Tactic

/-!
# Local symmetry factors in N₀ component orders

For a finite orientation C and an old successor-closed part P, the
local automorphisms are the digraph automorphisms of C fixing P
pointwise. This is the group whose cardinality is g_A(B) when C is
the successor closure of the component B and P = C \ B.

Fix one enumeration e of C. The transported enumerations h ∘ e
for distinct automorphisms h are distinct. Consequently the number
of permitted *transported enumerations* equals the size of the
pointwise stabilizer. No arbitrary ordering of the outgoing
neighbours is introduced.

This does not yet prove that the transported enumerations are exactly
the locally permitted linear orders of the manuscript, nor any
infinite big Ramsey statement.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (O : FiniteOrientation V)

/-- An automorphism of the complete finite orientation that fixes
the lower successor part P pointwise. -/
def IsPointwiseLowerAutomorphism
    (P : Finset V) (h : Equiv.Perm V) : Prop :=
  (∀ x y : V, y ∈ O.out x ↔ h y ∈ O.out (h x)) ∧
  (∀ x : V, x ∈ P → h x = x)

/-- The pointwise stabilizer of P in the orientation automorphism
group, represented as an actual finite set of permutations. -/
noncomputable def pointwiseLowerAutomorphisms
    (P : Finset V) : Finset (Equiv.Perm V) := by
  classical
  exact Finset.univ.filter (O.IsPointwiseLowerAutomorphism P)

/-- The identity is a local automorphism for every lower part. -/
theorem isPointwiseLowerAutomorphism_refl (P : Finset V) :
    O.IsPointwiseLowerAutomorphism P (Equiv.refl V) := by
  constructor
  · intro x y
    simp
  · intro x hx
    rfl

/-- The local pointwise stabilizer is never empty. -/
theorem pointwiseLowerAutomorphisms_nonempty (P : Finset V) :
    (O.pointwiseLowerAutomorphisms P).Nonempty := by
  classical
  refine ⟨Equiv.refl V, ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, O.isPointwiseLowerAutomorphism_refl P⟩

/-- Transport a fixed enumeration by a permutation of the vertices.
An enumeration is a bijection from a finite ordinal, not yet an
unlabelled linear-order relation. -/
def transportedLocalEnumeration {n : ℕ}
    (e : Fin n ≃ V) (h : Equiv.Perm V) : Fin n → V :=
  fun i => h (e i)

/-- The action on complete enumerations is free: if two
permutations transport every ordinal position equally, they
are literally equal. -/
theorem transportedLocalEnumeration_injective {n : ℕ}
    (e : Fin n ≃ V) :
    Function.Injective (transportedLocalEnumeration e) := by
  intro h k heq
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := e.surjective x
  exact congrFun heq i

/-- The number of transported complete enumerations is exactly
the size of the local pointwise stabilizer. -/
theorem localEnumeration_orbit_card
    (P : Finset V) {n : ℕ} (e : Fin n ≃ V) :
    ((O.pointwiseLowerAutomorphisms P).image
      (transportedLocalEnumeration e)).card =
    (O.pointwiseLowerAutomorphisms P).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro h hh k hk heq
  exact transportedLocalEnumeration_injective e heq

/-- A transported enumeration agrees with the original on the
points belonging to P: automorphisms counted by the local factor
cannot move the ordered lower successor part. -/
theorem transportedLocalEnumeration_fixed_lower
    (P : Finset V) {n : ℕ} (e : Fin n ≃ V)
    {h : Equiv.Perm V}
    (hh : h ∈ O.pointwiseLowerAutomorphisms P)
    (i : Fin n) (hi : e i ∈ P) :
    transportedLocalEnumeration e h i = e i := by
  classical
  have hfix := ((Finset.mem_filter.mp hh).2).2
  exact hfix (e i) hi

end FiniteOrientation
end BigHrushovski
