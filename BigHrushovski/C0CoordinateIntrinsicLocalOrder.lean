import BigHrushovski.C0CoordinateOrderedAgeBridge
import BigHrushovski.C0IntrinsicComponents

/-!
# Intrinsic top components and ordered lower closures in finite C₀

The complete unary operation, rather than the particular enumeration
of minimal strong blocks, determines each closure-component. The
top component of C(a) consists of those vertices with the same
complete unary value as a. Its complement in C(a) is the lower
closure P(a), which is itself closed and lies entirely before the
top component in any chronological component order.

These statements isolate the lower-ordered-part interface needed for
the manuscript's fixed representatives of one-generated closure types.
They do not choose a representative, construct W, or identify the full
ordered Fraïssé age.
-/

namespace BigHrushovski
namespace FiniteUnaryCoordinates

variable {V : Type*} [Fintype V] [LinearOrder V] [DecidableEq V]
variable {n : ℕ}

/-- The closure-component of a is intrinsic to the full unary
function: equality of complete one-generated values. -/
noncomputable def unaryComponentClass
    (C : V → Finset V) (a : V) : Finset V :=
  Finset.univ.filter (fun b => C b = C a)

/-- The lower part of the one-generated closure of a, obtained by
deleting precisely its intrinsic closure-component. -/
noncomputable def unaryLowerClosure
    (C : V → Finset V) (a : V) : Finset V :=
  C a \ unaryComponentClass C a

/-- The intrinsic component class agrees exactly with the whole
minimal-strong enumeration block. No generator is distinguished. -/
theorem canonical_unaryComponentClass_eq
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    unaryComponentClass (FiniteC0.canonicalValue G κ) a =
      FiniteC0.component κ (κ a).val := by
  exact (FiniteC0.component_eq_unary_value_class G κ a).symm

/-- A vertex in the lower closure belongs to an earlier component.
This follows solely from the decreasing back-dependency relation. -/
theorem canonical_unaryLowerClosure_subset_old
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    unaryLowerClosure (FiniteC0.canonicalValue G κ) a ⊆
      FiniteC0.oldStage κ (κ a).val := by
  intro b hb
  obtain ⟨hbC, hbNot⟩ := Finset.mem_sdiff.mp hb
  have hNotEq : κ b ≠ κ a := by
    intro heq
    apply hbNot
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ b,
      (FiniteC0.canonicalValue_eq_iff_index_eq G κ b a).mpr heq⟩
  have hLe : (κ b).val ≤ (κ a).val :=
    FiniteC0.canonicalAncestor_index_le G κ
      ((FiniteC0.mem_canonicalValue_iff G κ a b).mp hbC)
  apply (FiniteC0.mem_oldStage_iff κ (κ a).val b).mpr
  have hneq : (κ b).val ≠ (κ a).val := by
    intro heq
    exact hNotEq (Fin.ext heq)
  omega

/-- The full one-generated closure splits into its closed lower
part and the whole top component. -/
theorem canonical_lower_union_component
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    FiniteC0.canonicalValue G κ a =
      unaryLowerClosure (FiniteC0.canonicalValue G κ) a ∪
        unaryComponentClass (FiniteC0.canonicalValue G κ) a := by
  have hTop : unaryComponentClass (FiniteC0.canonicalValue G κ) a ⊆
      FiniteC0.canonicalValue G κ a := by
    rw [canonical_unaryComponentClass_eq G κ a]
    exact FiniteC0.canonicalValue_contains_component
      G κ (κ a).val
        ((FiniteC0.mem_component_iff κ (κ a).val a).mpr rfl)
  ext v
  constructor
  · intro hv
    by_cases hB : v ∈
        unaryComponentClass (FiniteC0.canonicalValue G κ) a
    · exact Finset.mem_union.mpr (Or.inr hB)
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hv, hB⟩))
  · intro hv
    rcases Finset.mem_union.mp hv with hl | hb
    · exact (Finset.mem_sdiff.mp hl).1
    · exact hTop hb

/-- The intrinsic lower closure is closed under the complete C₀
unary function. This is the property needed to treat it as a full
functional substructure rather than merely an induced graph. -/
theorem canonical_unaryLowerClosure_closed
    (G : GraphOn V) (κ : V → Fin n) (a : V) :
    ClosedUnder (FiniteC0.canonicalValue G κ)
      (unaryLowerClosure (FiniteC0.canonicalValue G κ) a) := by
  intro b hb c hbc
  have hbC : b ∈ FiniteC0.canonicalValue G κ a :=
    (Finset.mem_sdiff.mp hb).1
  have hcC : c ∈ FiniteC0.canonicalValue G κ a :=
    FiniteC0.canonicalValue_mem_trans G κ hbC hbc
  have hbOld : b ∈ FiniteC0.oldStage κ (κ a).val :=
    canonical_unaryLowerClosure_subset_old G κ a hb
  have hcOld : c ∈ FiniteC0.oldStage κ (κ a).val :=
    FiniteC0.canonicalValue_subset_oldStage G κ
      (κ a).val b hbOld hbc
  have hcNot : c ∉
      unaryComponentClass (FiniteC0.canonicalValue G κ) a := by
    intro hTop
    have hIndex : κ c = κ a :=
      (FiniteC0.canonicalValue_eq_iff_index_eq G κ c a).mp
        ((Finset.mem_filter.mp hTop).2)
    have hBefore : (κ c).val < (κ a).val :=
      (FiniteC0.mem_oldStage_iff κ (κ a).val c).mp hcOld
    omega
  exact Finset.mem_sdiff.mpr ⟨hcC, hcNot⟩

/-- In a chronological component order, every vertex of the lower
closure precedes every vertex of its top component. This does not
choose a particular order within either part. -/
theorem canonical_lower_before_top
    (G : GraphOn V) (κ : V → Fin n)
    (hOrder : ChronologicalBlockOrder κ) (a : V)
    {b c : V}
    (hb : b ∈ unaryLowerClosure
      (FiniteC0.canonicalValue G κ) a)
    (hc : c ∈ unaryComponentClass
      (FiniteC0.canonicalValue G κ) a) : b < c := by
  have hOld : b ∈ FiniteC0.oldStage κ (κ a).val :=
    canonical_unaryLowerClosure_subset_old G κ a hb
  have hlt : (κ b).val < (κ a).val :=
    (FiniteC0.mem_oldStage_iff κ (κ a).val b).mp hOld
  have hEq : κ c = κ a :=
    (FiniteC0.canonicalValue_eq_iff_index_eq G κ c a).mp
      ((Finset.mem_filter.mp hc).2)
  apply hOrder b c
  change (κ b).val < (κ c).val
  rw [hEq]
  exact hlt

end FiniteUnaryCoordinates
end BigHrushovski
