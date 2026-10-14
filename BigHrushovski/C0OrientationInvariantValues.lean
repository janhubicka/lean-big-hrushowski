import BigHrushovski.C0CommonBaseComponents
import BigHrushovski.C0IndependentComponentSwap

/-!
# Canonical C0 unary values depend only on the component partition and edge orientation

Two chronological indexings of a finite graph need not place
independent components in the same order. The complete unary
function nevertheless remains unchanged whenever:

* two vertices have the same index in one presentation exactly
  when they have the same index in the other;
* every edge between distinct components has the same chronological
  direction in both presentations.

The proof transfers each complete backward dependency path by
replacing the edge witnesses of its successive components. This
avoids any choice of distinguished representative for a component.

This is the unary-function half of the adjacent-swap argument.
Minimality of the swapped graph steps is separately certified
by GraphOn.independent_minimal_components_commute.
-/

namespace BigHrushovski
namespace FiniteC0

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {n m : ℕ}

/-- A backwards path in one finite component presentation can be
transported into another which has the same component partition
and orients every intercomponent graph edge in the same direction.

The endpoint is named by an actual vertex, so unused component
indices cause no problem. -/
theorem canonicalAncestor_transfer
    (G : GraphOn V) (κ : V → Fin n) (η : V → Fin m)
    (hSame : ∀ u v : V, κ u = κ v ↔ η u = η v)
    (hOrient : ∀ u v : V, G.adj u v →
      ((κ u).val < (κ v).val ↔ (η u).val < (η v).val))
    (root : V) {i : Fin n}
    (h : TaggedAmalgam.DependencyAncestor
      (backDependency G κ) (κ root) i) :
    ∃ v : V, κ v = i ∧
      TaggedAmalgam.DependencyAncestor
        (backDependency G η) (η root) (η v) := by
  induction h with
  | root =>
      exact ⟨root, rfl, TaggedAmalgam.DependencyAncestor.root⟩
  | @step a b ha hDep ih =>
      obtain ⟨w, hw, hOld⟩ := ih
      obtain ⟨hLt, u, v, hu, hv, hAdj⟩ := hDep
      have hSameOld : κ w = κ u := hw.trans hu.symm
      have hSameNew : η w = η u :=
        (hSame w u).mp hSameOld
      have hLtNew : (η v).val < (η u).val :=
        (hOrient v u (G.symm u v hAdj)).mp (by
          rw [hu, hv] at hLt
          exact hLt)
      have hDepNew : backDependency G η (η u) (η v) :=
        ⟨hLtNew, u, v, rfl, rfl, hAdj⟩
      have hOldU : TaggedAmalgam.DependencyAncestor
          (backDependency G η) (η root) (η u) := by
        rw [← hSameNew]
        exact hOld
      exact ⟨v, hv,
        TaggedAmalgam.DependencyAncestor.step hOldU hDepNew⟩

/-- The *complete* canonical set-valued unary functions agree
when the component partitions and directions of all actual
intercomponent edges agree. No minimality or two-sparsity
assumption is needed. -/
theorem canonicalValue_eq_of_component_partition_and_edge_orientation
    (G : GraphOn V) (κ : V → Fin n) (η : V → Fin m)
    (hSame : ∀ u v : V, κ u = κ v ↔ η u = η v)
    (hOrient : ∀ u v : V, G.adj u v →
      ((κ u).val < (κ v).val ↔ (η u).val < (η v).val))
    (root : V) :
    canonicalValue G κ root = canonicalValue G η root := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hwIndex, hReach⟩ :=
      canonicalAncestor_transfer G κ η hSame hOrient root
        ((mem_canonicalValue_iff G κ root v).mp hv)
    have hTargetIndex : η w = η v :=
      (hSame w v).mp hwIndex
    apply (mem_canonicalValue_iff G η root v).mpr
    rwa [hTargetIndex] at hReach
  · intro hv
    have hSameReverse : ∀ u v : V,
        η u = η v ↔ κ u = κ v :=
      fun u v => (hSame u v).symm
    have hOrientReverse : ∀ u v : V, G.adj u v →
        ((η u).val < (η v).val ↔ (κ u).val < (κ v).val) :=
      fun u v hAdj => (hOrient u v hAdj).symm
    obtain ⟨w, hwIndex, hReach⟩ :=
      canonicalAncestor_transfer G η κ
        hSameReverse hOrientReverse root
        ((mem_canonicalValue_iff G η root v).mp hv)
    have hTargetIndex : κ w = κ v :=
      (hSameReverse w v).mp hwIndex
    apply (mem_canonicalValue_iff G κ root v).mpr
    rwa [hTargetIndex] at hReach

end FiniteC0
end BigHrushovski
