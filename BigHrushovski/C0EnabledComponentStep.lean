import BigHrushovski.C0CountableOneComponentInterval
import BigHrushovski.C0CountableIntrinsicComponents

/-!
# Countable C₀: adjoining an enabled intrinsic component

Suppose Q is a finite set closed under the complete unary operation C,
x is not in Q, and every strict predecessor of the intrinsic component
of x is already in Q. Then adjoining the whole class of vertices whose
complete C-values agree with C(x) gives a finite closed set. The
extension by this class is minimal strong, and the new set is globally
strong in the original countable graph.

This is the one-step induction needed for the fair enumeration of
intrinsic finite components. It does not construct the enumeration.
-/

namespace BigHrushovski
namespace FiniteC0

/-- A closed prefix containing every strict predecessor remains closed
when the whole intrinsic component of x is added. No exclusion
hypothesis on x is needed for this closure statement. -/
theorem canonicalStages_enabledComponent_closed
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q)
    (x : ℕ) (hLower : strictLowerValue C x ⊆ Q) :
    N.IsClosedUnderValues C (Q ∪ unaryComponent C x) := by
  classical
  have hC : IsCompleteUnaryClosure C :=
    completeUnary_of_canonicalFiniteStages N C stage hCover hStage
  intro y hy z hz
  rcases Finset.mem_union.mp hy with hyQ | hyP
  · exact Finset.mem_union.mpr
      (Or.inl (hClosedQ y hyQ z hz))
  · have hCy : C y = C x :=
      (mem_unaryComponent_iff C hC x y).mp hyP
    have hzCx : z ∈ C x := by
      rw [← hCy]
      exact hz
    by_cases hzP : z ∈ unaryComponent C x
    · exact Finset.mem_union.mpr (Or.inr hzP)
    · have hzLower : z ∈ strictLowerValue C x :=
        Finset.mem_sdiff.mpr ⟨hzCx, hzP⟩
      exact Finset.mem_union.mpr (Or.inl (hLower hzLower))

/-- For a unary-closed Q, excluding x excludes its entire intrinsic
component: membership of any classmate would force x into Q by
reflexivity and complete unary-value equality. -/
theorem closed_disjoint_component_of_not_mem
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (hC : IsCompleteUnaryClosure C)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q)
    (x : ℕ) (hxNotQ : x ∉ Q) :
    Disjoint Q (unaryComponent C x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hyQ hyP
  have hCy : C y = C x :=
    (mem_unaryComponent_iff C hC x y).mp hyP
  have hxCy : x ∈ C y := by
    rw [hCy]
    exact hC.1 x
  exact hxNotQ (hClosedQ y hyQ x hxCy)

/-- An enabled component is one whose strict predecessors are already
present in a finite unary-closed Q. Adding an unlisted enabled
component is a minimal strong extension in the ambient countable graph.
No chronology or chosen generator inside the component is assumed. -/
theorem canonicalStages_enabledComponent_minimal
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q)
    (x : ℕ) (hxNotQ : x ∉ Q)
    (hLower : strictLowerValue C x ⊆ Q) :
    N.toPredimension.IsMinimalStrongStep
      Q (Q ∪ unaryComponent C x) := by
  classical
  have hC : IsCompleteUnaryClosure C :=
    completeUnary_of_canonicalFiniteStages N C stage hCover hStage
  have hDisj : Disjoint Q (unaryComponent C x) :=
    closed_disjoint_component_of_not_mem
      N C hC Q hClosedQ x hxNotQ
  have hDiff :
      ∀ y : ℕ, y ∈ (Q ∪ unaryComponent C x) \ Q ↔
        C y = C x := by
    intro y
    constructor
    · intro hy
      obtain ⟨hyZ, hyNotQ⟩ := Finset.mem_sdiff.mp hy
      rcases Finset.mem_union.mp hyZ with hyQ | hyP
      · exact (hyNotQ hyQ).elim
      · exact (mem_unaryComponent_iff C hC x y).mp hyP
    · intro hyEq
      have hyP : y ∈ unaryComponent C x :=
        (mem_unaryComponent_iff C hC x y).mpr hyEq
      have hyNotQ : y ∉ Q := by
        intro hyQ
        exact (Finset.disjoint_left.mp hDisj) hyQ hyP
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union.mpr (Or.inr hyP), hyNotQ⟩
  exact canonicalStages_oneComponentInterval_minimal
    N C stage hCover hStage
    Q (Q ∪ unaryComponent C x)
    Finset.subset_union_left
    hClosedQ
    (canonicalStages_enabledComponent_closed
      N C stage hCover hStage Q hClosedQ x hLower)
    x hDiff

/-- The new prefix is also globally strong, not only strong inside
one finite witnessing stage. -/
theorem canonicalStages_enabledComponent_globalStrong
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q)
    (x : ℕ) (hLower : strictLowerValue C x ⊆ Q) :
    N.toPredimension.IsGloballyStrong
      (Q ∪ unaryComponent C x) := by
  exact canonicalStages_closed_globalStrong
    N C stage hCover hStage (Q ∪ unaryComponent C x)
    (canonicalStages_enabledComponent_closed
      N C stage hCover hStage Q hClosedQ x hLower)

/-- The induction step for a prospective fair component enumeration:
the fresh component is minimal strong, and the resulting finite prefix
is globally strong. This does not assert existence of an enumeration. -/
theorem canonicalStages_enabledComponent_step_and_strong
    (N : GraphOn ℕ) (C : ℕ → Finset ℕ)
    (stage : ℕ → Finset ℕ)
    (hCover : ∀ b : Finset ℕ, ∃ n : ℕ, b ⊆ stage n)
    (hStage : HasCanonicalFiniteStages N C stage)
    (Q : Finset ℕ) (hClosedQ : N.IsClosedUnderValues C Q)
    (x : ℕ) (hxNotQ : x ∉ Q)
    (hLower : strictLowerValue C x ⊆ Q) :
    N.toPredimension.IsMinimalStrongStep
      Q (Q ∪ unaryComponent C x) ∧
    N.toPredimension.IsGloballyStrong
      (Q ∪ unaryComponent C x) := by
  exact ⟨canonicalStages_enabledComponent_minimal
      N C stage hCover hStage Q hClosedQ x hxNotQ hLower,
    canonicalStages_enabledComponent_globalStrong
      N C stage hCover hStage Q hClosedQ x hLower⟩

end FiniteC0
end BigHrushovski
