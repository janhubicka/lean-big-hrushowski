import BigHrushovski.C0CompleteUnaryCovers
import BigHrushovski.C0IntrinsicComponents

/-!
# Intrinsic finite closure-components of a complete unary operation

A complete one-generated set-valued unary operation C is reflexive and
transitive, and every value C(x) is finite. The class of vertices with
the same complete value as x is therefore itself finite: if C(y)=C(x),
then reflexivity gives y∈C(x).

These finite classes partition even an infinite carrier. They agree
with the minimal strong components in every finite canonical C₀
presentation, independently of the witnessing component chronology.

For y∈C(x) outside the component of x, C(y) is a proper subset of
C(x). Consequently the lower-component dependencies are finite and
strictly decrease the cardinality of a complete closure. This is the
finite-predecessor interface needed for a closure-component enumeration
of the countable functional limit. It does not itself select such an
enumeration or assert that each equality class is unary-closed.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [DecidableEq V]

/-- The intrinsic component of x is its complete unary-value class.
It is a finite set even when the carrier V is infinite. -/
noncomputable def unaryComponent (C : V → Finset V) (x : V) : Finset V :=
  (C x).filter (fun y => C y = C x)

/-- For a complete unary operation, membership in the finite component
is *equivalent* to equality of the two entire unary values. -/
theorem mem_unaryComponent_iff
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    (x y : V) :
    y ∈ unaryComponent C x ↔ C y = C x := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    rw [← h]
    exact hC.1 y

/-- Every vertex belongs to its own intrinsic component. -/
theorem mem_unaryComponent_self
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    (x : V) : x ∈ unaryComponent C x :=
  (mem_unaryComponent_iff C hC x x).mpr rfl

/-- Intrinsic components are finite subsets of their complete closures. -/
theorem unaryComponent_subset_value
    (C : V → Finset V) (x : V) :
    unaryComponent C x ⊆ C x := by
  classical
  exact Finset.filter_subset _ _

/-- Equality of complete values makes the intrinsic component sets equal. -/
theorem unaryComponent_eq_of_value_eq
    (C : V → Finset V) (x y : V)
    (hEq : C x = C y) :
    unaryComponent C x = unaryComponent C y := by
  classical
  simp only [unaryComponent, hEq]

/-- The intrinsic components form genuine disjoint-or-equal classes.
A vertex cannot belong to two classes with different full values. -/
theorem unaryComponents_disjoint_of_value_ne
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    (x y : V) (hNe : C x ≠ C y) :
    Disjoint (unaryComponent C x) (unaryComponent C y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzX hzY
  have hZX := (mem_unaryComponent_iff C hC x z).mp hzX
  have hZY := (mem_unaryComponent_iff C hC y z).mp hzY
  exact hNe (hZX.symm.trans hZY)

/-- The intrinsic component is exactly the old minimal-strong component
of any finite canonical presentation. No ordering of its vertices or
special generating point is selected. -/
theorem unaryComponent_eq_canonical_component
    [Fintype V] (G : GraphOn V) {n : ℕ}
    (κ : V → Fin n) (x : V) :
    unaryComponent (canonicalValue G κ) x =
      component κ (κ x).val := by
  classical
  let C : V → Finset V := canonicalValue G κ
  have hC : IsCompleteUnaryClosure C :=
    canonicalValue_isComplete G κ
  ext y
  constructor
  · intro hy
    have hValue : C y = C x :=
      (mem_unaryComponent_iff C hC x y).mp hy
    have hIndex : κ y = κ x :=
      (canonicalValue_eq_iff_index_eq G κ y x).mp hValue
    exact (mem_component_iff κ (κ x).val y).mpr
      (congrArg Fin.val hIndex)
  · intro hy
    have hIndex : κ y = κ x := Fin.ext
      ((mem_component_iff κ (κ x).val y).mp hy)
    apply (mem_unaryComponent_iff C hC x y).mpr
    exact (canonicalValue_eq_iff_index_eq G κ y x).mpr hIndex

/-- Everything in a complete unary value but outside its own intrinsic
component belongs to a strictly lower complete closure. -/
noncomputable def strictLowerValue (C : V → Finset V)
    (x : V) : Finset V :=
  (C x) \ unaryComponent C x

/-- A vertex below x but outside its component has a *properly*
smaller complete value, not just a subset. -/
theorem strictLowerValue_ssubset
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    {x y : V} (hy : y ∈ strictLowerValue C x) :
    C y ⊂ C x := by
  classical
  have hyC : y ∈ C x := (Finset.mem_sdiff.mp hy).1
  have hNe : C y ≠ C x := by
    intro hEq
    exact (Finset.mem_sdiff.mp hy).2
      ((mem_unaryComponent_iff C hC x y).mpr hEq)
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨hC.2 x y hyC, hNe⟩

/-- Each strict downward dependency decreases the size of the full
finite unary closure; infinite descending chains are impossible. -/
theorem strictLowerValue_card_lt
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    {x y : V} (hy : y ∈ strictLowerValue C x) :
    (C y).card < (C x).card := by
  exact Finset.card_lt_card (strictLowerValue_ssubset C hC hy)

/-- If C(y) is properly below C(x), the *whole* intrinsic component of
y lies in the finite set of strict lower vertices of x. -/
theorem unaryComponent_subset_strictLower
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    {x y : V} (hy : y ∈ C x) (hNe : C y ≠ C x) :
    unaryComponent C y ⊆ strictLowerValue C x := by
  classical
  intro z hz
  have hZY : C z = C y :=
    (mem_unaryComponent_iff C hC y z).mp hz
  have hZC : z ∈ C x :=
    (hC.2 x y hy) (unaryComponent_subset_value C y hz)
  have hZNot : z ∉ unaryComponent C x := by
    intro hZX
    have hZXValue : C z = C x :=
      (mem_unaryComponent_iff C hC x z).mp hZX
    exact hNe (hZY.symm.trans hZXValue)
  exact Finset.mem_sdiff.mpr ⟨hZC, hZNot⟩

end FiniteC0
end BigHrushovski
