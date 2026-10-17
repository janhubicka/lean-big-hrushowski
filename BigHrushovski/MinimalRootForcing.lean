import BigHrushovski.CFDClosedGenerators
import BigHrushovski.C0FiniteStrongFactorization

/-!
# Root forcing in finite minimal closure extensions

This lemma is common to the C_0 strong-component and C_F strict
d-closed-block arguments. A finite closed set X, inside a finite
ambient set C, cannot meet a minimal closed increment B\A in a new
vertex while containing A without also containing *all* of B,
provided B itself is closed in C.

The proof only needs the intersection and restriction properties
of the chosen closure relation; it does not use the growth
function F, a linear order, an enumeration, or countability.

The ambient requirement B <= C is important. Being minimal over
A only inside B does not by itself say that the intersection
X∩B is closed in B when B is not closed in C.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V]

/-- Common finite intersection argument for both strongness and
strict d-closedness. The relation Closed is assumed to be closed
under intersections and restrictions inside the same ambient set.
The only minimality hypothesis is about proper intermediate
Closed sets between A and B. -/
theorem minimal_block_forced_by_root
    (Closed : Finset V → Finset V → Prop)
    (hSubset : ∀ {p q : Finset V}, Closed p q → p ⊆ q)
    (hInter : ∀ {p q c : Finset V},
      Closed p c → Closed q c → Closed (p ∩ q) c)
    (hRestrict : ∀ {p q c : Finset V},
      Closed p c → p ⊆ q → q ⊆ c → Closed p q)
    {a b c x : Finset V}
    (hab : a ⊆ b)
    (hBC : Closed b c)
    (hXC : Closed x c)
    (hAX : a ⊆ x)
    (hMinimal : ∀ z : Finset V,
      a ⊆ z → z ⊆ b → Closed z b → z = a ∨ z = b)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x := by
  have hIntersectC : Closed (x ∩ b) c :=
    hInter hXC hBC
  have hIntersectB : Closed (x ∩ b) b :=
    hRestrict hIntersectC Finset.inter_subset_right (hSubset hBC)
  have hAIntersect : a ⊆ x ∩ b := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hAX hv, hab hv⟩
  rcases hMinimal (x ∩ b) hAIntersect Finset.inter_subset_right
      hIntersectB with hEq | hEq
  · have hr : r ∈ a := by
      rw [← hEq]
      exact Finset.mem_inter.mpr ⟨hrX, hrB⟩
    exact (hrA hr).elim
  · intro v hvB
    have hv : v ∈ x ∩ b := by
      rw [hEq]
      exact hvB
    exact (Finset.mem_inter.mp hv).1

variable (d : Predimension V)

/-- If a finite globally strong X contains a base A and a new
vertex of a minimal strong component A < B, then X contains B,
provided B is globally strong in the same finite ambient C. -/
theorem minimalStrongStep_forced_by_root
    {a b c x : Finset V}
    (hStep : d.IsMinimalStrongStep a b)
    (hBC : d.IsStrong b c)
    (hXC : d.IsStrong x c)
    (hAX : a ⊆ x)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x :=
  minimal_block_forced_by_root d.IsStrong
    (fun hp => hp.1)
    (fun hp hq => d.strong_inter hp hq)
    (fun hp hpq hqc => d.strong_restrict hp hpq hqc)
    hStep.1.1 hBC hXC hAX hStep.2.2 r hrB hrA hrX

/-- Strict d-closed analogue, needed to recover an entire
C_F block from its first vertex and the already recovered
earlier support. Weak self-sufficiency is not substituted for
strict closure. -/
theorem minimalDClosedStep_forced_by_root
    {a b c x : Finset V}
    (hStep : d.IsMinimalDClosedStep a b)
    (hBC : d.IsDClosed b c)
    (hXC : d.IsDClosed x c)
    (hAX : a ⊆ x)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x :=
  minimal_block_forced_by_root d.IsDClosed
    (fun hp => hp.1)
    (fun hp hq => d.dclosed_inter hp hq)
    (fun hp hpq hqc => d.dclosed_restrict hp hpq hqc)
    hStep.1.1 hBC hXC hAX hStep.2.2 r hrB hrA hrX

end Predimension
end BigHrushovski
