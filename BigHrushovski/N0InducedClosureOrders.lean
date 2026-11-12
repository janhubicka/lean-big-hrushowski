import BigHrushovski.N0GlobalComponentSignature
import BigHrushovski.N0CanonicalLocalOrders
import Mathlib.Tactic

/-!
# Restricting actual finite orders to successor closures

A complete finite vertex enumeration induces a uniquely determined
enumeration on each finite subset: list its vertices in the same relative
order, ignoring the other vertices. We implement this construction using
the finite order isomorphism for the order inherited from the original
enumeration, so that its ordinal index has exactly the size of the
restricted subset.

The comparison theorem is literal equality of all old-old comparisons;
no graph isomorphism, new arbitrary order or quotient by automorphisms
enters. In particular we can restrict to the *actual* successor
closure C_B and apply the canonical local adjacency-code criterion.

This still does not establish the global counting bijection.
-/

namespace BigHrushovski
namespace FiniteOrientation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Enumerate a finite subset S in the relative order inherited
from a complete enumeration e of the ambient labelled vertex set. -/
noncomputable def inducedEnumerationOn {n : ℕ}
    (e : Fin n ≃ V) (S : Finset V) :
    Fin (Fintype.card (↥S)) ≃ (↥S) := by
  classical
  letI : LinearOrder (↥S) :=
    LinearOrder.lift' (fun u : ↥S => e.symm u.val)
      (by
        intro u v h
        exact Subtype.ext (e.symm.injective h))
  exact (Fintype.orderIsoFinOfCardEq (↥S) rfl).toEquiv

/-- The induced enumeration has *exactly* the relative order of e
on S, including comparisons of nonadjacent vertices. -/
theorem inducedEnumerationOn_order_iff {n : ℕ}
    (e : Fin n ≃ V) (S : Finset V) (u v : ↥S) :
    OrderBefore (inducedEnumerationOn e S) u v ↔
      OrderBefore e u.val v.val := by
  classical
  letI : LinearOrder (↥S) :=
    LinearOrder.lift' (fun z : ↥S => e.symm z.val)
      (by
        intro z w h
        exact Subtype.ext (e.symm.injective h))
  let E : Fin (Fintype.card (↥S)) ≃o (↥S) :=
    Fintype.orderIsoFinOfCardEq (↥S) rfl
  change E.symm u < E.symm v ↔
    e.symm u.val < e.symm v.val
  change E.symm u < E.symm v ↔ u < v
  constructor
  · intro huv
    simpa using E.strictMono huv
  · intro huv
    exact E.symm.strictMono huv

/-- Relative order is unchanged when a subset is first viewed
inside a larger subset. This prevents spurious dependence on
unrelated ambient vertices. -/
theorem inducedEnumerationOn_restrict_twice {n : ℕ}
    (e : Fin n ≃ V) {S T : Finset V} (hST : S ⊆ T)
    (u v : ↥S) :
    OrderBefore (inducedEnumerationOn e S) u v ↔
      OrderBefore (inducedEnumerationOn e T)
        (⟨u.val, hST u.property⟩ : ↥T)
        (⟨v.val, hST v.property⟩ : ↥T) := by
  calc
    OrderBefore (inducedEnumerationOn e S) u v ↔
        OrderBefore e u.val v.val :=
      inducedEnumerationOn_order_iff e S u v
    _ ↔ OrderBefore (inducedEnumerationOn e T)
          (⟨u.val, hST u.property⟩ : ↥T)
          (⟨v.val, hST v.property⟩ : ↥T) :=
      (inducedEnumerationOn_order_iff e T
        (⟨u.val, hST u.property⟩ : ↥T)
        (⟨v.val, hST v.property⟩ : ↥T)).symm

/-- An induced enumeration depends only on the inherited
pairwise comparisons, not the positions of vertices outside S. -/
theorem inducedEnumerationOn_eq_of_order_agree
    {n m : ℕ} (e : Fin n ≃ V) (f : Fin m ≃ V)
    (S : Finset V)
    (hAgree : ∀ u ∈ S, ∀ v ∈ S,
      (OrderBefore e u v ↔ OrderBefore f u v)) :
    inducedEnumerationOn e S = inducedEnumerationOn f S := by
  apply enumeration_eq_of_same_order
    (inducedEnumerationOn e S) (inducedEnumerationOn f S)
  intro u v
  calc
    OrderBefore (inducedEnumerationOn e S) u v ↔
        OrderBefore e u.val v.val :=
      inducedEnumerationOn_order_iff e S u v
    _ ↔ OrderBefore f u.val v.val :=
      hAgree u.val u.property v.val v.property
    _ ↔ OrderBefore (inducedEnumerationOn f S) u v :=
      (inducedEnumerationOn_order_iff f S u v).symm

-- Used to form finite sets of literal labelled order relations.
noncomputable local instance : DecidableEq (V → V → Prop) :=
  Classical.decEq _

variable (O : FiniteOrientation V)

/-- The genuinely inherited enumeration of C_B for an actual
SCC generator x. The type of its carrier is the same as the
carrier used for the local induced orientation. -/
noncomputable def inheritedComponentEnumeration
    {n : ℕ} (e : Fin n ≃ V) (x : V) :
    Fin (Fintype.card (↥(O.componentClosure x))) ≃
      O.componentClosure x :=
  inducedEnumerationOn e (O.componentClosure x)

/-- Each comparison within the actual closure is inherited
literally from the global labelled order. -/
theorem inheritedComponentEnumeration_order_iff
    {n : ℕ} (e : Fin n ≃ V) (x : V)
    (u v : O.componentClosure x) :
    OrderBefore (O.inheritedComponentEnumeration e x) u v ↔
      OrderBefore e u.val v.val :=
  inducedEnumerationOn_order_iff e (O.componentClosure x) u v

/-- In a successor-first global order, P_B is strictly before B
also in the inherited complete enumeration of C_B. -/
theorem inheritedComponentEnumeration_lower_before_top
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e)
    (x : V)
    {u v : O.componentClosure x}
    (hu : u ∈ O.inducedLowerPart x)
    (hv : v.val ∈ O.component x) :
    OrderBefore (O.inheritedComponentEnumeration e x) u v := by
  apply (O.inheritedComponentEnumeration_order_iff e x u v).mpr
  exact O.successorFirst_lowerPart_before_component
    e he x ((O.mem_inducedLowerPart_iff x u).mp hu) hv

/-- An inherited order on P_B has the initial-segment property
in the restricted closure C_B (not in all of V). -/
theorem inheritedComponentEnumeration_lower_initial
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsSuccessorFirstEnumeration e) (x : V)
    {u v : O.componentClosure x}
    (hu : u ∈ O.inducedLowerPart x)
    (hvu : OrderBefore (O.inheritedComponentEnumeration e x) v u) :
    v ∈ O.inducedLowerPart x := by
  apply (O.mem_inducedLowerPart_iff x v).mpr
  exact O.successorFirst_lowerPart_initial_in_closure
    e he x
    ((O.mem_inducedLowerPart_iff x u).mp hu) v.property
    ((O.inheritedComponentEnumeration_order_iff e x v u).mp hvu)

/-- A finite *candidate* for the manuscript's locally canonical
successor-first component orders, using a fixed row-major
lexicographic complete-code convention. The exact manuscript
representatives, if chosen differently, require separate comparison. -/
def IsFiniteCanonicalComponentEnumeration
    {n : ℕ} (e : Fin n ≃ V) : Prop :=
  O.IsComponentIntervalEnumeration e ∧
  O.IsSuccessorFirstEnumeration e ∧
  ∀ x : V,
    O.inheritedComponentEnumeration e x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration e x)

/-- Every local inherited enumeration of a candidate global
canonical order is a genuine canonical enumerated closure. -/
theorem finiteCanonical_inherited_component
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsFiniteCanonicalComponentEnumeration e)
    (x : V) :
    O.inheritedComponentEnumeration e x ∈
      O.canonicalComponentLexClass x
        (O.inheritedComponentEnumeration e x) :=
  he.2.2 x

/-- In particular every inherited local *order relation* belongs
to the actual canonical labelled-order class with its prescribed
lower part. This is a forward direction only. -/
theorem finiteCanonical_inherited_order
    {n : ℕ} (e : Fin n ≃ V)
    (he : O.IsFiniteCanonicalComponentEnumeration e)
    (x : V) :
    OrderBefore (O.inheritedComponentEnumeration e x) ∈
      O.canonicalComponentOrderRelations x
        (O.inheritedComponentEnumeration e x) := by
  classical
  change OrderBefore (O.inheritedComponentEnumeration e x) ∈
    (O.canonicalComponentLexClass x
      (O.inheritedComponentEnumeration e x)).image OrderBefore
  exact Finset.mem_image.mpr
    ⟨O.inheritedComponentEnumeration e x,
      O.finiteCanonical_inherited_component e he x, rfl⟩

/-- Actual global enumerations satisfying the stated finite
canonical condition: no synthetic independent factor choices. -/
noncomputable def finiteCanonicalComponentEnumerations {n : ℕ} :
    Finset (Fin n ≃ V) := by
  classical
  exact Finset.univ.filter O.IsFiniteCanonicalComponentEnumeration

/-- Membership is the *global* finite canonical condition, not
merely the product of local cardinalities. -/
theorem mem_finiteCanonicalComponentEnumerations
    {n : ℕ} (e : Fin n ≃ V) :
    e ∈ O.finiteCanonicalComponentEnumerations ↔
      O.IsFiniteCanonicalComponentEnumeration e := by
  classical
  simp [finiteCanonicalComponentEnumerations]

/-- The number of distinct strict labelled global orders in the
candidate family is exactly its number of enumerations. -/
theorem finiteCanonicalGlobalOrderRelations_card {n : ℕ} :
    ((O.finiteCanonicalComponentEnumerations (n := n)).image
      OrderBefore).card =
      (O.finiteCanonicalComponentEnumerations (n := n)).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro e _ f _ h
  exact orderBefore_injective h

end FiniteOrientation
end BigHrushovski
