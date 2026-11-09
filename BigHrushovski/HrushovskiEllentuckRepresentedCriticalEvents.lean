import BigHrushovski.HrushovskiEllentuckCriticalEvents

/-!
# The induced map on represented rational critical events

The quaternary height-comparison relation on coding leaves identifies
equal pair-meet events, including diagonal pairs, provided distinct
events have distinct heights. This file turns the comparison result into
an actual map on *represented* critical events. We prove that this map
does not depend on a chosen pair representing the source event, is a
bijection onto the events represented by mapped pairs, and preserves
and reflects their height order.

This is the represented-event fragment of the rational similarity
argument. It does not yet prove ancestry, left/right order, passing
types, critical frontier completion, a coding-tree similarity, or the
correspondence with actual (R,H) functional copies.
-/

namespace BigHrushovski.Ellentuck

universe u v w z

variable {A : Type u} {B : Type v} {E : Type w} {F : Type z}

/-- Critical events that are actually represented by a pair of coding
leaves (diagonal pairs included). -/
def RepresentedCriticalEvent (event : A → A → E) : Type w :=
  {e : E // ∃ a b : A, event a b = e}

/-- Select an arbitrary representing pair of each source event, then
apply f to that pair. Comparison preservation below ensures that the
resulting event is independent of this choice. Target events are
restricted to the mapped pairs; no assertion about all target events
is hidden in the codomain. -/
noncomputable def representedCriticalEventMap
    (eventA : A → A → E) (eventB : B → B → F) (f : A → B) :
    RepresentedCriticalEvent eventA →
      RepresentedCriticalEvent
        (fun a b : A => eventB (f a) (f b)) := by
  intro e
  classical
  let a : A := Classical.choose e.property
  let b : A := Classical.choose (Classical.choose_spec e.property)
  exact ⟨eventB (f a) (f b), ⟨a, b, rfl⟩⟩

/-- The induced event is independent of the chosen representation,
by equality reflection of *all* pair-meet height comparisons. -/
theorem representedCriticalEventMap_apply
    (eventA : A → A → E) (eventB : B → B → F)
    (levelA : E → ℕ) (levelB : F → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons
      (fun a b => levelA (eventA a b))
      (fun a b => levelB (eventB a b)) f)
    (hinjA : Function.Injective levelA)
    (hinjB : Function.Injective levelB)
    (e : RepresentedCriticalEvent eventA)
    (x y : A) (hxy : eventA x y = e.1) :
    (representedCriticalEventMap eventA eventB f e).1 =
      eventB (f x) (f y) := by
  classical
  let a : A := Classical.choose e.property
  let b : A := Classical.choose (Classical.choose_spec e.property)
  have hab : eventA a b = e.1 :=
    Classical.choose_spec (Classical.choose_spec e.property)
  have hSource : eventA a b = eventA x y := hab.trans hxy.symm
  have hTarget : eventB (f a) (f b) = eventB (f x) (f y) :=
    (criticalEvent_eq_iff_of_comparisons eventA eventB
      levelA levelB f hcmp hinjA hinjB a b x y).mp hSource
  change eventB (f a) (f b) = eventB (f x) (f y)
  exact hTarget

/-- Full event equality is reflected: two represented source events
have the same image precisely when they were equal in the source. -/
theorem representedCriticalEventMap_injective
    (eventA : A → A → E) (eventB : B → B → F)
    (levelA : E → ℕ) (levelB : F → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons
      (fun a b => levelA (eventA a b))
      (fun a b => levelB (eventB a b)) f)
    (hinjA : Function.Injective levelA)
    (hinjB : Function.Injective levelB) :
    Function.Injective (representedCriticalEventMap eventA eventB f) := by
  intro e e' heq
  classical
  let a : A := Classical.choose e.property
  let b : A := Classical.choose (Classical.choose_spec e.property)
  let c : A := Classical.choose e'.property
  let d : A := Classical.choose (Classical.choose_spec e'.property)
  have hab : eventA a b = e.1 :=
    Classical.choose_spec (Classical.choose_spec e.property)
  have hcd : eventA c d = e'.1 :=
    Classical.choose_spec (Classical.choose_spec e'.property)
  have he1 := representedCriticalEventMap_apply
    eventA eventB levelA levelB f hcmp hinjA hinjB e a b hab
  have he2 := representedCriticalEventMap_apply
    eventA eventB levelA levelB f hcmp hinjA hinjB e' c d hcd
  have hImages : eventB (f a) (f b) = eventB (f c) (f d) := by
    calc
      eventB (f a) (f b) =
          (representedCriticalEventMap eventA eventB f e).1 := he1.symm
      _ = (representedCriticalEventMap eventA eventB f e').1 :=
        congrArg Subtype.val heq
      _ = eventB (f c) (f d) := he2
  have hSource : eventA a b = eventA c d :=
    (criticalEvent_eq_iff_of_comparisons eventA eventB
      levelA levelB f hcmp hinjA hinjB a b c d).mpr hImages
  apply Subtype.ext
  exact hab.symm.trans (hSource.trans hcd)

/-- Every target event represented by some mapped pair is obtained
from the corresponding represented source event. We do not claim
that all events of the ambient target coding tree are represented. -/
theorem representedCriticalEventMap_surjective
    (eventA : A → A → E) (eventB : B → B → F)
    (levelA : E → ℕ) (levelB : F → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons
      (fun a b => levelA (eventA a b))
      (fun a b => levelB (eventB a b)) f)
    (hinjA : Function.Injective levelA)
    (hinjB : Function.Injective levelB) :
    Function.Surjective (representedCriticalEventMap eventA eventB f) := by
  intro e
  obtain ⟨a, b, hab⟩ := e.property
  let src : RepresentedCriticalEvent eventA :=
    ⟨eventA a b, ⟨a, b, rfl⟩⟩
  refine ⟨src, ?_⟩
  apply Subtype.ext
  calc
    (representedCriticalEventMap eventA eventB f src).1 =
        eventB (f a) (f b) :=
      representedCriticalEventMap_apply
        eventA eventB levelA levelB f hcmp hinjA hinjB src a b rfl
    _ = e.1 := hab

/-- The induced map preserves and reflects the order of critical
heights, even when distinct pair representations denote one event.
This is height order, not yet the full ancestry/passing-type relation. -/
theorem representedCriticalEventMap_level_le_iff
    (eventA : A → A → E) (eventB : B → B → F)
    (levelA : E → ℕ) (levelB : F → ℕ)
    (f : A → B)
    (hcmp : PreservesMeetHeightComparisons
      (fun a b => levelA (eventA a b))
      (fun a b => levelB (eventB a b)) f)
    (hinjA : Function.Injective levelA)
    (hinjB : Function.Injective levelB)
    (e e' : RepresentedCriticalEvent eventA) :
    levelA e.1 ≤ levelA e'.1 ↔
      levelB (representedCriticalEventMap eventA eventB f e).1 ≤
        levelB (representedCriticalEventMap eventA eventB f e').1 := by
  classical
  let a : A := Classical.choose e.property
  let b : A := Classical.choose (Classical.choose_spec e.property)
  let c : A := Classical.choose e'.property
  let d : A := Classical.choose (Classical.choose_spec e'.property)
  have hab : eventA a b = e.1 :=
    Classical.choose_spec (Classical.choose_spec e.property)
  have hcd : eventA c d = e'.1 :=
    Classical.choose_spec (Classical.choose_spec e'.property)
  have he1 := representedCriticalEventMap_apply
    eventA eventB levelA levelB f hcmp hinjA hinjB e a b hab
  have he2 := representedCriticalEventMap_apply
    eventA eventB levelA levelB f hcmp hinjA hinjB e' c d hcd
  have hComparison :=
    meetHeight_le_iff_of_comparisons
      (fun x y => levelA (eventA x y))
      (fun x y => levelB (eventB x y))
      f hcmp a b c d
  constructor
  · intro h
    rw [he1, he2]
    exact hComparison.mp (by simpa only [hab, hcd] using h)
  · intro h
    have ht : levelB (eventB (f a) (f b)) ≤
        levelB (eventB (f c) (f d)) := by
      simpa only [he1, he2] using h
    exact (by simpa only [hab, hcd] using hComparison.mpr ht)

end BigHrushovski.Ellentuck
