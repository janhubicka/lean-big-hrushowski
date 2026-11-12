import BigHrushovski.C0CoordinateCoherentLocalOrders
import BigHrushovski.C0CoordinateIntrinsicLowerChoice

/-!
# Hereditary local catalogues: it suffices to check the lower part

The definition `ChosenLocalOrders.IsHereditary` checks restrictions
of a selected local type to C(a) for every vertex a.

For a top vertex, C(a) is the whole representative. Thus the chosen
type itself and the identity-on-vertices equivalence witness this
restriction automatically. The only genuine compatibility checks are
for a in the ordered lower part.

This reduction is independent of the existence of an age-wide complete
catalogue. It makes the remaining induction obligation smaller; it
does not supply that catalogue.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {I : Type*}

/-- Hereditary compatibility only for vertices of the ordered lower
part. As in the full definition, all graph pairs, all complete unary
values, the inherited order and the intrinsic lower part are required. -/
def ChosenLocalOrders.IsLowerHereditary
    (c : ChosenLocalOrders I) : Prop :=
  ∀ (i : I) (a : Fin (c.size i)),
    a ∈ (c.representative i).lower →
    ∃ j : I,
      ∃ f : Fin (c.size j) ≃ (c.representative i).value a,
        (∀ u v : Fin (c.size j),
          (c.representative j).graph.adj u v ↔
            (c.representative i).graph.adj
              (f u).val (f v).val) ∧
        (∀ u v : Fin (c.size j),
          v ∈ (c.representative j).value u ↔
            (f v).val ∈ (c.representative i).value (f u).val) ∧
        (∀ u v : Fin (c.size j),
          u < v ↔ (f u).val < (f v).val) ∧
        (∀ u : Fin (c.size j),
          u ∈ (c.representative j).lower ↔
            (c.representative i).value (f u).val ≠
              (c.representative i).value a)

/-- Every top generator already has the required hereditary
certificate: the chosen representative is compared with itself.
There is no implicit assumption of rigidity or uniqueness of an
unordered generating top vertex. -/
theorem ChosenLocalOrders.top_restriction_compatible
    (c : ChosenLocalOrders I)
    (i : I) (a : Fin (c.size i))
    (ha : a ∉ (c.representative i).lower) :
    ∃ j : I,
      ∃ f : Fin (c.size j) ≃ (c.representative i).value a,
        (∀ u v : Fin (c.size j),
          (c.representative j).graph.adj u v ↔
            (c.representative i).graph.adj
              (f u).val (f v).val) ∧
        (∀ u v : Fin (c.size j),
          v ∈ (c.representative j).value u ↔
            (f v).val ∈ (c.representative i).value (f u).val) ∧
        (∀ u v : Fin (c.size j),
          u < v ↔ (f u).val < (f v).val) ∧
        (∀ u : Fin (c.size j),
          u ∈ (c.representative j).lower ↔
            (c.representative i).value (f u).val ≠
              (c.representative i).value a) := by
  classical
  let r := c.representative i
  have hGen : r.value a = Finset.univ :=
    r.top_generates a ha
  let f : Fin (c.size i) ≃ r.value a :=
    { toFun := fun u => ⟨u, by
        rw [hGen]
        exact Finset.mem_univ u⟩
      invFun := fun u => u.val
      left_inv := fun _ => rfl
      right_inv := by
        intro u
        apply Subtype.ext
        rfl }
  refine ⟨i, f, ?_, ?_, ?_, ?_⟩
  · intro u v
    change r.graph.adj u v ↔ r.graph.adj u v
    rfl
  · intro u v
    change v ∈ r.value u ↔ v ∈ r.value u
    rfl
  · intro u v
    change u < v ↔ u < v
    rfl
  · intro u
    change u ∈ r.lower ↔ r.value u ≠ r.value a
    rw [hGen]
    exact r.mem_lower_iff_value_ne_univ u

/-- A catalogue is hereditary exactly when the one-generated
restrictions of its lower vertices are compatible. Restrictions
at its top vertices are automatic and introduce no further
choice of order. -/
theorem ChosenLocalOrders.isHereditary_iff_isLowerHereditary
    (c : ChosenLocalOrders I) :
    c.IsHereditary ↔ c.IsLowerHereditary := by
  constructor
  · intro h i a _ha
    exact h i a
  · intro h i a
    by_cases ha : a ∈ (c.representative i).lower
    · exact h i a ha
    · exact c.top_restriction_compatible i a ha

/-- Assemble the existing hereditary-catalogue interface from a
certificate only concerning lower vertices. This proves no catalogue
exists; it merely avoids restating the automatic top case. -/
def HereditaryLocalOrders.ofLower
    (c : ChosenLocalOrders I)
    (h : c.IsLowerHereditary) :
    HereditaryLocalOrders I where
  choices := c
  restriction_compatible :=
    (c.isHereditary_iff_isLowerHereditary).mpr h

end FiniteUnaryCoordinates
end BigHrushovski
