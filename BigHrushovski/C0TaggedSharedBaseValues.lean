import BigHrushovski.C0TaggedCanonicalBoth
import BigHrushovski.C0CommonBaseComponents

/-!
# Concrete two-sided unary transport from the shared named base

The tagged C0 free graph is made from G on P⊕L and H on P⊕R.
Both factors have complete canonical unary values and identify the
same named unary function F:P→Finset P on their common closed base.

From that SINGLE shared base value equality we derive:
* the same intrinsic base component partition;
* the same orientation of every edge between base components;
* closedness of the base under the full unary value.

The right presentation is frontloaded, so all base components
precede its fresh components. The actual joined component index
keeps every left component rank and appends the right tail.

The conclusion is simultaneous preservation of every complete
vertex-valued unary value along BOTH literal tagged injections.
Neither this conclusion nor component/rank compatibility is
assumed by the final theorem.
-/
namespace BigHrushovski
namespace TaggedAmalgam

variable {P L R : Type*}
variable [Fintype P] [Fintype L] [Fintype R]
variable [DecidableEq P] [DecidableEq L] [DecidableEq R]
variable {n m : ℕ}

/-- Membership of the named base vertex in the image of a named
base finite subset is independent of the ambient left/right type. -/
private theorem mem_base_image_iff_left
    (S : Finset P) (p : P) :
    (Sum.inl p : Sum P L) ∈ S.image
      (Sum.inl : P → Sum P L) ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp h
    have heq : q = p := Sum.inl_injective hEq
    simpa [heq] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

private theorem mem_base_image_iff_right
    (S : Finset P) (p : P) :
    (Sum.inl p : Sum P R) ∈ S.image
      (Sum.inl : P → Sum P R) ↔ p ∈ S := by
  constructor
  · intro h
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp h
    have heq : q = p := Sum.inl_injective hEq
    simpa [heq] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- Shared canonical unary values on the base force agreement of
all base edge directions, even when the two witnessing chronological
orders are entirely different on incomparable components. -/
theorem namedBase_edge_orientation
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (F : P → Finset P)
    (hG : ∀ p : P,
      FiniteC0.canonicalValue G κL (.inl p) =
        (F p).image (Sum.inl : P → Sum P L))
    (hH : ∀ p : P,
      FiniteC0.canonicalValue H κR (.inl p) =
        (F p).image (Sum.inl : P → Sum P R))
    (hComp : ∀ p q : P,
      κL (.inl p) = κL (.inl q) ↔
      κR (.inl p) = κR (.inl q))
    (p q : P) (hpq : H.adj (.inl p) (.inl q)) :
    ((κL (.inl p)).val < (κL (.inl q)).val ↔
     (κR (.inl p)).val < (κR (.inl q)).val) := by
  by_cases hSame : κL (.inl p) = κL (.inl q)
  · have hSameR : κR (.inl p) = κR (.inl q) :=
      (hComp p q).mp hSame
    have hEqL := congrArg Fin.val hSame
    have hEqR := congrArg Fin.val hSameR
    constructor <;> intro hLt <;> omega
  · have hDiffR : κR (.inl p) ≠ κR (.inl q) := by
      intro heq
      exact hSame ((hComp p q).mpr heq)
    have hpqL : G.adj (.inl p) (.inl q) :=
      (hAgree p q).mpr hpq
    have hLeft :=
      FiniteC0.adjacent_order_iff_unary_membership
        G κL (.inl p) (.inl q) hpqL hSame
    have hRight :=
      FiniteC0.adjacent_order_iff_unary_membership
        H κR (.inl p) (.inl q) hpq hDiffR
    have hMem :
      (Sum.inl p : Sum P L) ∈
        FiniteC0.canonicalValue G κL (.inl q) ↔
      (Sum.inl p : Sum P R) ∈
        FiniteC0.canonicalValue H κR (.inl q) := by
      rw [hG q, hH q]
      exact (mem_base_image_iff_left (F q) p).trans
        (mem_base_image_iff_right (F q) p).symm
    exact hLeft.trans (hMem.trans hRight.symm)

/-- A base whose complete named unary values are wholly on P is
closed in the original left factor. -/
theorem namedBase_left_closed
    (G : GraphOn (Sum P L)) (κL : Sum P L → Fin n)
    (F : P → Finset P)
    (hG : ∀ p : P,
      FiniteC0.canonicalValue G κL (.inl p) =
        (F p).image (Sum.inl : P → Sum P L)) :
    G.IsClosedUnderValues
      (FiniteC0.canonicalValue G κL)
      ((Finset.univ : Finset P).image
        (Sum.inl : P → Sum P L)) := by
  intro x hx y hy
  obtain ⟨p, _, hEq⟩ := Finset.mem_image.mp hx
  rw [← hEq] at hy
  rw [hG p] at hy
  exact Finset.mem_image.mpr (by
    obtain ⟨q, hq, hqy⟩ := Finset.mem_image.mp hy
    exact ⟨q, Finset.mem_univ _, hqy⟩)

/-- Complete finite two-sided unary transport on the ACTUAL free graph:
the named common unary values imply all partition, orientation,
and closure conditions needed by the tagged canonical index theorem. -/
theorem taggedCanonicalValues_both_of_named_base
    (G : GraphOn (Sum P L)) (H : GraphOn (Sum P R))
    (hAgree : AgreeBase G H)
    (κL : Sum P L → Fin n) (κR : Sum P R → Fin m)
    (F : P → Finset P)
    (hG : ∀ p : P,
      FiniteC0.canonicalValue G κL (.inl p) =
        (F p).image (Sum.inl : P → Sum P L))
    (hH : ∀ p : P,
      FiniteC0.canonicalValue H κR (.inl p) =
        (F p).image (Sum.inl : P → Sum P R))
    (hFront : ∀ p : P, ∀ r : R,
      (κR (.inl p)).val < (κR (.inr r)).val) :
    (∀ u : Sum P L,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (leftTag u) =
      (FiniteC0.canonicalValue G κL u).image
        (leftTag : Sum P L → Carrier P L R)) ∧
    (∀ u : Sum P R,
      FiniteC0.canonicalValue (freeGraph G H)
        (joinedIndex κL κR) (rightTag u) =
      (FiniteC0.canonicalValue H κR u).image
        (rightTag : Sum P R → Carrier P L R)) := by
  have hComp : ∀ p q : P,
      κL (.inl p) = κL (.inl q) ↔
      κR (.inl p) = κR (.inl q) :=
    FiniteC0.common_component_partition_of_shared_unary_values
      G H κL κR
      (Sum.inl : P → Sum P L)
      (Sum.inl : P → Sum P R)
      (by intro x y h; exact Sum.inl_injective h)
      (by intro x y h; exact Sum.inl_injective h)
      F hG hH
  have hOrient : ∀ p q : P,
      H.adj (.inl p) (.inl q) →
      ((κL (.inl p)).val < (κL (.inl q)).val ↔
       (κR (.inl p)).val < (κR (.inl q)).val) :=
    namedBase_edge_orientation G H hAgree κL κR F hG hH hComp
  have hClosed := namedBase_left_closed G κL F hG
  exact taggedCanonicalValues_both G H hAgree κL κR
    hComp hFront hOrient hClosed

end TaggedAmalgam
end BigHrushovski
