import BigHrushovski.C0CountableCanonicalStages
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


/-- Every complete value splits into its intrinsic component and the
strictly lower vertices, with no omitted vertices. -/
theorem completeValue_eq_component_union_lower
    (C : V → Finset V) (x : V) :
    C x = unaryComponent C x ∪ strictLowerValue C x := by
  classical
  ext y
  constructor
  · intro hy
    by_cases hp : y ∈ unaryComponent C x
    · exact Finset.mem_union.mpr (Or.inl hp)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hy, hp⟩))
  · intro hy
    rcases Finset.mem_union.mp hy with hp | hl
    · exact unaryComponent_subset_value C x hp
    · exact (Finset.mem_sdiff.mp hl).1

/-- The new component is disjoint from its complete strict-lower
dependency set; this does not require any closure hypotheses. -/
theorem component_disjoint_strictLower
    (C : V → Finset V) (x : V) :
    Disjoint (unaryComponent C x) (strictLowerValue C x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hp hl
  exact (Finset.mem_sdiff.mp hl).2 hp

/-- Removing all strict predecessors from the complete closure leaves
exactly the intrinsic component, including every vertex in it. -/
theorem component_eq_value_sdiff_lower
    (C : V → Finset V) (x : V) :
    unaryComponent C x = C x \ strictLowerValue C x := by
  classical
  ext y
  constructor
  · intro hp
    refine Finset.mem_sdiff.mpr
      ⟨unaryComponent_subset_value C x hp, ?_⟩
    intro hl
    exact (Finset.mem_sdiff.mp hl).2 hp
  · intro hy
    have hyC : y ∈ C x := (Finset.mem_sdiff.mp hy).1
    by_contra hp
    have hl : y ∈ strictLowerValue C x :=
      Finset.mem_sdiff.mpr ⟨hyC, hp⟩
    exact (Finset.mem_sdiff.mp hy).2 hl

/-- The strict lower dependency set of a complete value is itself
closed under the whole finite unary operation. This uses full
transitivity, not just direct backward-neighbour closure. -/
theorem strictLowerValue_closed
    (C : V → Finset V) (hC : IsCompleteUnaryClosure C)
    (x : V) :
    ∀ y ∈ strictLowerValue C x, C y ⊆ strictLowerValue C x := by
  classical
  intro y hy z hz
  have hyC : y ∈ C x := (Finset.mem_sdiff.mp hy).1
  have hzC : z ∈ C x := (hC.2 x y hyC) hz
  have hyCard : (C y).card < (C x).card :=
    strictLowerValue_card_lt C hC hy
  have hzCard : (C z).card ≤ (C y).card :=
    Finset.card_le_card (hC.2 y z hz)
  have hzNot : z ∉ unaryComponent C x := by
    intro hp
    have hEq : C z = C x :=
      (mem_unaryComponent_iff C hC x z).mp hp
    have hEqCard : (C z).card = (C x).card :=
      congrArg Finset.card hEq
    omega
  exact Finset.mem_sdiff.mpr ⟨hzC, hzNot⟩

/-- The strict-lower set is a genuine finite functionally closed
substructure in any graph on the carrier. -/
theorem strictLowerValue_isClosedUnderValues
    (N : GraphOn V) (C : V → Finset V)
    (hC : IsCompleteUnaryClosure C) (x : V) :
    N.IsClosedUnderValues C (strictLowerValue C x) := by
  intro y hy z hz
  exact strictLowerValue_closed C hC x y hy hz

/-- The countable finite-canonical-stage criterion makes *every*
finite unary-closed set globally strong, not merely strong in each
particular witnessing stage. -/
theorem canonicalStages_closed_globalStrong
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (s : Finset ℕ) (hClosed : N.IsClosedUnderValues C s) :
    N.toPredimension.IsGloballyStrong s := by
  intro b hb
  obtain ⟨n, hn⟩ := hCover b
  have hs : s ⊆ stage n := hb.trans hn
  have hStrong : N.toPredimension.IsStrong s (stage n) :=
    localStrong_of_canonicalFiniteStages N C stage hStage
      n s hs hClosed
  exact N.toPredimension.strong_restrict hStrong hb hn

/-- In a countable C₀ structure with exact finite canonical stages,
the strict dependencies of any component form a finite globally strong
set. This is the intrinsic initial cut for a one-component extension. -/
theorem intrinsicLower_globalStrong_of_canonicalStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (x : ℕ) :
    N.toPredimension.IsGloballyStrong (strictLowerValue C x) := by
  have hC : IsCompleteUnaryClosure C :=
    completeUnary_of_canonicalFiniteStages N C stage hCover hStage
  exact canonicalStages_closed_globalStrong
    N C stage hCover hStage
    (strictLowerValue C x)
    (strictLowerValue_isClosedUnderValues N C hC x)

/-- The full finite closure of a component is also globally strong
under the same hypotheses; its difference from the preceding cut is
exactly the intrinsic component. -/
theorem intrinsicValue_globalStrong_of_canonicalStages
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (x : ℕ) :
    N.toPredimension.IsGloballyStrong (C x) := by
  have hC : IsCompleteUnaryClosure C :=
    completeUnary_of_canonicalFiniteStages N C stage hCover hStage
  have hClosed : N.IsClosedUnderValues C (C x) := by
    intro y hy z hz
    exact (hC.2 x y hy) hz
  exact canonicalStages_closed_globalStrong
    N C stage hCover hStage (C x) hClosed


end FiniteC0
end BigHrushovski
