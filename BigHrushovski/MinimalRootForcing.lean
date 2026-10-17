import BigHrushovski.CFDClosedGenerators
import BigHrushovski.C0FiniteStrongFactorization

/-!
# Root forcing in finite minimal closure extensions

A closed set X in a finite ambient graph C which contains a base
A and at least one point of a minimal extension A < B must contain
all of B. In fact, it is enough that B ⊆ C: the endpoint B need
not itself be closed in C.

The key observation is the *intersection-restriction lemma*:
if X is strong (respectively strictly d-closed) in C and B ⊆ C,
then X∩B is strong (respectively strictly d-closed) in B. This
follows directly from submodularity. Together with minimality,
it gives the one-root forcing lemma in both C_0 and C_F.

The final theorem iterates this implication along a finite chain
of rooted minimal d-closed extensions, showing that the old base
and one marked new vertex from each increment generate the
entire final set by strict d-closure. This is the finite input to
the block-root reconstruction in the manuscript. The countable
birth-block induction and equality H(R(v))=C(v) remain separate.
-/

namespace BigHrushovski
namespace Predimension

variable {V : Type*} [DecidableEq V] (d : Predimension V)

/-- Intersect a finite strong substructure with any finite
intermediate vertex set, which need not itself be strong in C. -/
theorem strong_inter_restrict
    {x b c : Finset V}
    (hXC : d.IsStrong x c) (hBC : b ⊆ c) :
    d.IsStrong (x ∩ b) b := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro y hXY hYB
  have hCap : x ∩ y = x ∩ b := by
    apply le_antisymm
    · intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1,
         hYB (Finset.mem_inter.mp hv).2⟩
    · intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1, hXY hv⟩
  have hUnion : x ∪ y ⊆ c :=
    Finset.union_subset hXC.1 (hYB.trans hBC)
  have hDelta : d.delta x ≤ d.delta (x ∪ y) :=
    hXC.2 (x ∪ y) Finset.subset_union_left hUnion
  have hSub := d.submodular x y
  rw [hCap] at hSub
  omega

/-- Strict intersection restriction: finite d-closedness
restricts to every finite vertex subset, without requiring
that subset to be d-closed in the larger ambient graph. -/
theorem dclosed_inter_restrict
    {x b c : Finset V}
    (hXC : d.IsDClosed x c) (hBC : b ⊆ c) :
    d.IsDClosed (x ∩ b) b := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro y hXY hNe hYB
  have hCap : x ∩ y = x ∩ b := by
    apply le_antisymm
    · intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1,
         hYB (Finset.mem_inter.mp hv).2⟩
    · intro v hv
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hv).1, hXY hv⟩
  have hNotSub : ¬ y ⊆ x := by
    intro hyx
    have hYX : y ⊆ x ∩ b := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨hyx hv, hYB hv⟩
    exact hNe (le_antisymm hYX hXY)
  have hUnionNe : x ∪ y ≠ x := by
    intro hEq
    apply hNotSub
    intro v hv
    have hvU : v ∈ x ∪ y := Finset.mem_union.mpr (Or.inr hv)
    rw [hEq] at hvU
    exact hvU
  have hUnion : x ∪ y ⊆ c :=
    Finset.union_subset hXC.1 (hYB.trans hBC)
  have hDelta : d.delta x < d.delta (x ∪ y) :=
    hXC.2 (x ∪ y) Finset.subset_union_left hUnionNe hUnion
  have hSub := d.submodular x y
  rw [hCap] at hSub
  omega

/-- A finite minimal step is forced by any single new vertex
inside a closed ambient set. This relation-parametric form
is the common argument for strong and strict d-closed steps. -/
theorem minimal_block_forced_by_root
    (Closed : Finset V → Finset V → Prop)
    (hIntersect : ∀ {x b c : Finset V},
      Closed x c → b ⊆ c → Closed (x ∩ b) b)
    {a b c x : Finset V}
    (hab : a ⊆ b) (hBC : b ⊆ c)
    (hXC : Closed x c) (hAX : a ⊆ x)
    (hMinimal : ∀ z : Finset V,
      a ⊆ z → z ⊆ b → Closed z b → z = a ∨ z = b)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x := by
  have hIntersection : Closed (x ∩ b) b :=
    hIntersect hXC hBC
  have hAIntersect : a ⊆ x ∩ b := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hAX hv, hab hv⟩
  rcases hMinimal (x ∩ b) hAIntersect Finset.inter_subset_right
      hIntersection with hEq | hEq
  · have hr : r ∈ a := by
      rw [← hEq]
      exact Finset.mem_inter.mpr ⟨hrX, hrB⟩
    exact (hrA hr).elim
  · intro v hvB
    have hv : v ∈ x ∩ b := by
      rw [hEq]
      exact hvB
    exact (Finset.mem_inter.mp hv).1

/-- Weak strong-component version. No strongness assumption
on the minimal step's endpoint B in C is needed. -/
theorem minimalStrongStep_forced_by_root
    {a b c x : Finset V}
    (hStep : d.IsMinimalStrongStep a b)
    (hBC : b ⊆ c)
    (hXC : d.IsStrong x c)
    (hAX : a ⊆ x)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x :=
  minimal_block_forced_by_root d.IsStrong
    (fun hp hq => d.strong_inter_restrict hp hq)
    hStep.1.1 hBC hXC hAX hStep.2.2 r hrB hrA hrX

/-- Strict d-closed-block version, with no extra closure
hypothesis on B in C. -/
theorem minimalDClosedStep_forced_by_root
    {a b c x : Finset V}
    (hStep : d.IsMinimalDClosedStep a b)
    (hBC : b ⊆ c)
    (hXC : d.IsDClosed x c)
    (hAX : a ⊆ x)
    (r : V) (hrB : r ∈ b) (hrA : r ∉ a) (hrX : r ∈ x) :
    b ⊆ x :=
  minimal_block_forced_by_root d.IsDClosed
    (fun hp hq => d.dclosed_inter_restrict hp hq)
    hStep.1.1 hBC hXC hAX hStep.2.2 r hrB hrA hrX

/-- Finite minimal d-closed steps equipped with a chosen
new root from a common finite set of designated roots.
The roots may also include vertices of the original base. -/
inductive RootedMinimalDClosedChain (d : Predimension V)
    (roots : Finset V) : Finset V → Finset V → Prop where
  | refl (a : Finset V) : RootedMinimalDClosedChain d roots a a
  | step {a b c : Finset V}
      (hab : d.IsMinimalDClosedStep a b)
      (r : V) (hrRoots : r ∈ roots)
      (hrB : r ∈ b) (hrA : r ∉ a)
      (hTail : RootedMinimalDClosedChain d roots b c) :
      RootedMinimalDClosedChain d roots a c

/-- Every rooted finite chain is an increasing chain
of vertex subsets. -/
theorem RootedMinimalDClosedChain.subset
    {roots a b : Finset V}
    (chain : RootedMinimalDClosedChain d roots a b) :
    a ⊆ b := by
  induction chain with
  | refl a => exact Finset.Subset.rfl
  | step hStep r hrRoots hrB hrA hTail ih =>
      exact hStep.1.1.trans ih

/-- A d-closed set containing the initial base and all marked
roots of a finite rooted chain contains its entire last stage.
This is the step-by-step mechanism of block-root recovery. -/
theorem RootedMinimalDClosedChain.subset_of_closed
    {roots a b : Finset V}
    (chain : RootedMinimalDClosedChain d roots a b) :
    ∀ x : Finset V,
      d.IsDClosed x b → a ⊆ x → roots ⊆ x → b ⊆ x := by
  induction chain with
  | refl a =>
      intro x hx hAx hRoots
      exact hAx
  | @step a m b hStep r hrRoots hrM hrA hTail ih =>
      intro x hXB hAX hRoots
      have hMB : m ⊆ b :=
        RootedMinimalDClosedChain.subset d hTail
      have hMsubsetX : m ⊆ x :=
        d.minimalDClosedStep_forced_by_root
          hStep hMB hXB hAX r hrM hrA (hRoots hrRoots)
      exact ih x hXB hMsubsetX hRoots

/-- If the selected roots hit every minimal increment,
their d-closure together with the old base is exactly the
final vertex set. No unnecessary ambient-closure hypothesis
is imposed on intermediate steps. -/
theorem RootedMinimalDClosedChain.roots_generate
    {roots a b : Finset V}
    (chain : RootedMinimalDClosedChain d roots a b)
    (hRootsB : roots ⊆ b) :
    d.dClosedHull (a ∪ roots) b = b := by
  have hAB : a ⊆ b := chain.subset
  have hSource : a ∪ roots ⊆ b :=
    Finset.union_subset hAB hRootsB
  let x := d.dClosedHull (a ∪ roots) b
  have hX : d.IsDClosed x b :=
    d.dClosedHull_dclosed (a ∪ roots) b
  have hContained : a ∪ roots ⊆ x :=
    d.subset_dClosedHull hSource
  have hAX : a ⊆ x :=
    Finset.subset_union_left.trans hContained
  have hRootsX : roots ⊆ x :=
    Finset.subset_union_right.trans hContained
  exact le_antisymm hX.1
    (chain.subset_of_closed x hX hAX hRootsX)

end Predimension
end BigHrushovski
