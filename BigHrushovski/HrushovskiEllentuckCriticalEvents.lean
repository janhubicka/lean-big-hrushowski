import Mathlib

/-!
# Critical-event comparisons for the rational Ellentuck space

The rational case in Section 6b names a four-ary relation comparing
heights of pair meets, with repeated entries allowed. Equal critical
events may have different pair representations; comparison of all
pair-meet heights is therefore needed to show that the induced action
on events is well defined.

This module proves the representation-independent finite arithmetic
part of that claim. The event equality theorem uses the genuine
diagonal-antichain hypothesis that distinct critical events have
distinct lengths, expressed by injectivity of the event-height map.

No coding-tree similarity, passing-type preservation, Dobrinen theorem,
or rational functional embedding is asserted here.
-/

namespace BigHrushovski.Ellentuck

universe u v w z

variable {A : Type u} {B : Type v}

/-- Exact preservation and reflection of every quaternary comparison
of pair-meet heights. Diagonal pairs are permitted. -/
def PreservesMeetHeightComparisons
    (heightA : A → A → ℕ) (heightB : B → B → ℕ)
    (f : A → B) : Prop :=
  ∀ a b c d : A,
    (heightA a b < heightA c d ↔
      heightB (f a) (f b) < heightB (f c) (f d))

/-- The four-ary strict comparison table also determines equality
of all represented critical *heights*. No injectivity of f or
discreteness assumption on coding leaves is needed. -/
theorem meetHeight_eq_iff_of_comparisons
    (heightA : A → A → ℕ) (heightB : B → B → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons heightA heightB f)
    (a b c d : A) :
    heightA a b = heightA c d ↔
      heightB (f a) (f b) = heightB (f c) (f d) := by
  constructor
  · intro heq
    have hn1 : ¬ heightA a b < heightA c d := by omega
    have hn2 : ¬ heightA c d < heightA a b := by omega
    have hr1 : ¬ heightB (f a) (f b) < heightB (f c) (f d) := by
      intro hlt
      exact hn1 ((hcmp a b c d).mpr hlt)
    have hr2 : ¬ heightB (f c) (f d) < heightB (f a) (f b) := by
      intro hlt
      exact hn2 ((hcmp c d a b).mpr hlt)
    omega
  · intro heq
    have hn1 : ¬ heightB (f a) (f b) < heightB (f c) (f d) := by omega
    have hn2 : ¬ heightB (f c) (f d) < heightB (f a) (f b) := by omega
    have hl1 : ¬ heightA a b < heightA c d := by
      intro hlt
      exact hn1 ((hcmp a b c d).mp hlt)
    have hl2 : ¬ heightA c d < heightA a b := by
      intro hlt
      exact hn2 ((hcmp c d a b).mp hlt)
    omega

/-- Nonstrict critical-height order is also determined by the same
strict comparison table. In particular all ancestor tests of the
form |a ∧ b| ≤ |a ∧ x| are transported. -/
theorem meetHeight_le_iff_of_comparisons
    (heightA : A → A → ℕ) (heightB : B → B → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons heightA heightB f)
    (a b c d : A) :
    heightA a b ≤ heightA c d ↔
      heightB (f a) (f b) ≤ heightB (f c) (f d) := by
  constructor
  · intro hle
    have hn : ¬ heightA c d < heightA a b := by omega
    have hn' : ¬ heightB (f c) (f d) < heightB (f a) (f b) := by
      intro hh
      exact hn ((hcmp c d a b).mpr hh)
    omega
  · intro hle
    have hn : ¬ heightB (f c) (f d) < heightB (f a) (f b) := by omega
    have hn' : ¬ heightA c d < heightA a b := by
      intro hh
      exact hn ((hcmp c d a b).mp hh)
    omega

/-- When distinct critical events have distinct heights, equal
pair-meet representations are carried to equal target events,
and equality of target representations reflects equality at
the source. This is the well-definedness step in the paper's
extension of a coding-node map to critical events. -/
theorem criticalEvent_eq_iff_of_comparisons
    {E : Type w} {F : Type z}
    (eventA : A → A → E) (eventB : B → B → F)
    (levelA : E → ℕ) (levelB : F → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons
      (fun a b => levelA (eventA a b))
      (fun a b => levelB (eventB a b)) f)
    (hinjA : Function.Injective levelA)
    (hinjB : Function.Injective levelB)
    (a b c d : A) :
    eventA a b = eventA c d ↔
      eventB (f a) (f b) = eventB (f c) (f d) := by
  have hHeights :=
    meetHeight_eq_iff_of_comparisons
      (fun x y => levelA (eventA x y))
      (fun x y => levelB (eventB x y))
      f hcmp a b c d
  constructor
  · intro heq
    apply hinjB
    exact hHeights.mp (congrArg levelA heq)
  · intro heq
    apply hinjA
    exact hHeights.mpr (congrArg levelB heq)

/-- The diagonal-pair coding events are part of the same table:
their height order relative to every pair-meet is preserved. -/
theorem diagonal_meetHeight_le_iff
    (heightA : A → A → ℕ) (heightB : B → B → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons heightA heightB f)
    (a b c : A) :
    heightA a a ≤ heightA b c ↔
      heightB (f a) (f a) ≤ heightB (f b) (f c) :=
  meetHeight_le_iff_of_comparisons heightA heightB f hcmp a a b c

end BigHrushovski.Ellentuck
